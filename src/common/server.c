/* X-Chat
 * Copyright (C) 1998 Peter Zelezny.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301, USA
 *
 * MS Proxy (ISA server) support is (c) 2006 Pavel Fedin <sonic_amiga@rambler.ru>
 * based on Dante source code
 * Copyright (c) 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006
 *      Inferno Nettverk A/S, Norway.  All rights reserved.
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <errno.h>
#include <fcntl.h>

#ifdef WIN32
#include <winbase.h>
#include <io.h>
#else
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

#include "hexchat.h"
#include "fe.h"
#include "cfgfiles.h"
#include "notify.h"
#include "hexchatc.h"
#include "inbound.h"
#include "outbound.h"
#include "text.h"
#include "util.h"
#include "url.h"
#include "proto-irc.h"
#include "servlist.h"
#include "server.h"

#if !GLIB_CHECK_VERSION (2, 40, 0)
#define g_inet_socket_address_new_from_string(x,y) g_inet_socket_address_new(g_inet_address_new_from_string(x),y)
#endif

static GSList *away_list = NULL;
GSList *serv_list = NULL;

static void auto_reconnect (server *serv, int send_quit, char *err);
static void server_disconnect (session * sess, int sendquit, char *err);
static int server_cleanup (server * serv);
static void server_connect (server *serv, char *hostname, int port, int no_login);

/* actually send the text. This might do a character translation. server/dcc both use this function. */
int
tcp_send_real (GSocketConnection *conn, char *encoding, int using_irc, char *buf, int len)
{
	GOutputStream *stream;
	int ret;
	char *locale;
	gsize loc_len;

	stream = g_io_stream_get_output_stream (G_IO_STREAM(conn));
	g_assert (G_IS_OBJECT(stream));

	if (encoding == NULL)	/* system */
	{
		locale = NULL;
		if (!prefs.utf8_locale)
		{
			const gchar *charset;

			g_get_charset (&charset);
			locale = g_convert_with_fallback (buf, len, charset, "UTF-8",
														 "?", 0, &loc_len, 0);
		}
	} else
	{
		if (using_irc)	/* using "IRC" encoding (CP1252/UTF-8 hybrid) */
			/* if all chars fit inside CP1252, use that. Otherwise this
			   returns NULL and we send UTF-8. */
			locale = g_convert (buf, len, "CP1252", "UTF-8", 0, &loc_len, 0);
		else
			locale = g_convert_with_fallback (buf, len, encoding, "UTF-8",
														 "?", 0, &loc_len, 0);
	}

	if (locale)
	{
		len = loc_len;
		ret = g_output_stream_write_all (stream, locale, len, NULL, NULL, NULL);
		g_free (locale);
	} else
	{
		ret = g_output_stream_write_all (stream, buf, len, NULL, NULL, NULL);
	}

	return ret;
}

static int
server_send_real (server *serv, char *buf, int len)
{
	fe_add_rawlog (serv, buf, len, TRUE);

	url_check_line (buf, len);

	return tcp_send_real (serv->conn, serv->encoding, serv->using_irc,
								 buf, len);
}

/* new throttling system, uses the same method as the Undernet
   ircu2.10 server; under test, a 200-line paste didn't flood
   off the client */

static int
tcp_send_queue (server *serv)
{
	char *buf, *p;
	int len, i, pri;
	GSList *list;
	time_t now = time (0);

	/* did the server close since the timeout was added? */
	if (!is_server (serv))
		return 0;

	/* try priority 2,1,0 */
	pri = 2;
	while (pri >= 0)
	{
		list = serv->outbound_queue;
		while (list)
		{
			buf = (char *) list->data;
			if (buf[0] == pri)
			{
				buf++;	/* skip the priority byte */
				len = strlen (buf);

				if (serv->next_send < now)
					serv->next_send = now;
				if (serv->next_send - now >= 10)
				{
					/* check for clock skew */
					if (now >= serv->prev_now)
						return 1;		  /* don't remove the timeout handler */
					/* it is skewed, reset to something sane */
					serv->next_send = now;
				}

				for (p = buf, i = len; i && *p != ' '; p++, i--);
				serv->next_send += (2 + i / 120);
				serv->sendq_len -= len;
				serv->prev_now = now;
				fe_set_throttle (serv);

				server_send_real (serv, buf, len);

				buf--;
				serv->outbound_queue = g_slist_remove (serv->outbound_queue, buf);
				free (buf);
				list = serv->outbound_queue;
			} else
			{
				list = list->next;
			}
		}
		/* now try pri 0 */
		pri--;
	}
	return 0;						  /* remove the timeout handler */
}

int
tcp_send_len (server *serv, char *buf, int len)
{
	char *dbuf;
	int noqueue = !serv->outbound_queue;

	if (!prefs.hex_net_throttle)
		return server_send_real (serv, buf, len);

	dbuf = malloc (len + 2);	/* first byte is the priority */
	dbuf[0] = 2;	/* pri 2 for most things */
	memcpy (dbuf + 1, buf, len);
	dbuf[len + 1] = 0;

	/* privmsg and notice get a lower priority */
	if (g_ascii_strncasecmp (dbuf + 1, "PRIVMSG", 7) == 0 ||
		 g_ascii_strncasecmp (dbuf + 1, "NOTICE", 6) == 0)
	{
		dbuf[0] = 1;
	}
	else
	{
		/* WHO/MODE get the lowest priority */
		if (g_ascii_strncasecmp (dbuf + 1, "WHO ", 4) == 0 ||
		/* but only MODE queries, not changes */
			(g_ascii_strncasecmp (dbuf + 1, "MODE", 4) == 0 &&
			 strchr (dbuf, '-') == NULL &&
			 strchr (dbuf, '+') == NULL))
			dbuf[0] = 0;
	}

	serv->outbound_queue = g_slist_append (serv->outbound_queue, dbuf);
	serv->sendq_len += len; /* tcp_send_queue uses strlen */

	if (tcp_send_queue (serv) && noqueue)
		fe_timeout_add (500, tcp_send_queue, serv);

	return 1;
}

/*int
tcp_send (server *serv, char *buf)
{
	return tcp_send_len (serv, buf, strlen (buf));
}*/

void
tcp_sendf (server *serv, char *fmt, ...)
{
	va_list args;
	/* keep this buffer in BSS. Converting UTF-8 to ISO-8859-x might make the
      string shorter, so allow alot more than 512 for now. */
	static char send_buf[1540];	/* good code hey (no it's not overflowable) */
	int len;

	va_start (args, fmt);
	len = vsnprintf (send_buf, sizeof (send_buf) - 1, fmt, args);
	va_end (args);

	send_buf[sizeof (send_buf) - 1] = '\0';
	if (len < 0 || len > (sizeof (send_buf) - 1))
		len = strlen (send_buf);

	tcp_send_len (serv, send_buf, len);
}


/* handle 1 line of text received from the server */

static void
server_inline (server *serv, char *line, int len)
{
	char *utf_line_allocated = NULL;

	/* Checks whether we're set to use UTF-8 charset */
	if (serv->using_irc ||				/* 1. using CP1252/UTF-8 Hybrid */
		(serv->encoding == NULL && prefs.utf8_locale) || /* OR 2. using system default->UTF-8 */
	    (serv->encoding != NULL &&				/* OR 3. explicitly set to UTF-8 */
		 (g_ascii_strcasecmp (serv->encoding, "UTF8") == 0 ||
		  g_ascii_strcasecmp (serv->encoding, "UTF-8") == 0)))
	{
		/* The user has the UTF-8 charset set, either via /charset
		command or from his UTF-8 locale. Thus, we first try the
		UTF-8 charset, and if we fail to convert, we assume
		it to be ISO-8859-1 (see text_validate). */

		utf_line_allocated = text_validate (&line, &len);

	} else
	{
		/* Since the user has an explicit charset set, either
		via /charset command or from his non-UTF8 locale,
		we don't fallback to ISO-8859-1 and instead try to remove
		errnoeous octets till the string is convertable in the
		said charset. */

		const char *encoding = NULL;

		if (serv->encoding != NULL)
			encoding = serv->encoding;
		else
			g_get_charset (&encoding);

		if (encoding != NULL)
		{
			char *conv_line; /* holds a copy of the original string */
			int conv_len; /* tells g_convert how much of line to convert */
			gsize utf_len;
			gsize read_len;
			GError *err;
			gboolean retry;

			conv_line = g_malloc (len + 1);
			memcpy (conv_line, line, len);
			conv_line[len] = 0;
			conv_len = len;

			/* if CP1255, convert it with the NUL terminator.
				Works around SF bug #1122089 */
			if (serv->using_cp1255)
				conv_len++;

			do
			{
				err = NULL;
				retry = FALSE;
				utf_line_allocated = g_convert_with_fallback (conv_line, conv_len, "UTF-8", encoding, "?", &read_len, &utf_len, &err);
				if (err != NULL)
				{
					if (err->code == G_CONVERT_ERROR_ILLEGAL_SEQUENCE && conv_len > (read_len + 1))
					{
						/* Make our best bet by removing the erroneous char.
						   This will work for casual 8-bit strings with non-standard chars. */
						memmove (conv_line + read_len, conv_line + read_len + 1, conv_len - read_len -1);
						conv_len--;
						retry = TRUE;
					}
					g_error_free (err);
				}
			} while (retry);

			g_free (conv_line);

			/* If any conversion has occured at all. Conversion might fail
			due to errors other than invalid sequences, e.g. unknown charset. */
			if (utf_line_allocated != NULL)
			{
				line = utf_line_allocated;
				len = utf_len;
				if (serv->using_cp1255 && len > 0)
					len--;
			}
			else
			{
				/* If all fails, treat as UTF-8 with fallback to ISO-8859-1. */
				utf_line_allocated = text_validate (&line, &len);
			}
		}
	}

	fe_add_rawlog (serv, line, len, FALSE);

	/* let proto-irc.c handle it */
	serv->p_inline (serv, line, len);

	if (utf_line_allocated != NULL) /* only if a special copy was allocated */
		g_free (utf_line_allocated);
}

/* read data from socket */

static void
server_read (GInputStream *stream, GAsyncResult *res, server *serv)
{
	gsize len, i;
	gchar *err_msg;
	GError *error = NULL;

	g_assert (is_server(serv));

	len = g_input_stream_read_finish (stream, res, &error);
	if (!error)
	{
		i = 0;
		serv->in_buf[len] = 0;

		while (i < len)
		{
			switch (serv->in_buf[i])
			{
			case '\r':
				break;

			case '\n':
				serv->linebuf[serv->pos] = 0;
				server_inline (serv, serv->linebuf, serv->pos);
				serv->pos = 0;
				break;

			default:
				serv->linebuf[serv->pos] = serv->in_buf[i];
				if (serv->pos >= (sizeof (serv->linebuf) - 1))
					fprintf (stderr,
								"*** HEXCHAT WARNING: Buffer overflow - shit server!\n");
				else
					serv->pos++;
			}
			i++;
		}

		g_input_stream_read_async (stream, serv->in_buf, sizeof(serv->in_buf) - 2,
						G_PRIORITY_DEFAULT, NULL,
						(GAsyncReadyCallback)server_read, serv);
	}
	else
	{
		err_msg = error->message;
		g_printf ("%s\n", err_msg);
		if (!serv->end_of_motd)
		{
			server_disconnect (serv->server_session, FALSE, err_msg);
			if (!servlist_cycle (serv))
			{
				if (prefs.hex_net_auto_reconnect)
					auto_reconnect (serv, FALSE, err_msg);
			}
		} else
		{
			if (prefs.hex_net_auto_reconnect)
				auto_reconnect (serv, FALSE, err_msg);
			else
				server_disconnect (serv->server_session, FALSE, err_msg);
		}
		g_error_free (error);
	}
}

static void
server_connected (server * serv)
{
	prefs.wait_on_exit = TRUE;
	serv->ping_recv = time (0);
	serv->lag_sent = 0;
	serv->connected = TRUE;

	g_input_stream_read_async (g_io_stream_get_input_stream (G_IO_STREAM(serv->conn)),
						serv->in_buf, sizeof(serv->in_buf) - 2, G_PRIORITY_DEFAULT,
						NULL, (GAsyncReadyCallback)server_read, serv);

	if (!serv->no_login)
	{
		EMIT_SIGNAL (XP_TE_CONNECTED, serv->server_session, NULL, NULL, NULL,
						 NULL, 0);
		if (serv->network)
		{
			serv->p_login (serv,
								(!(((ircnet *)serv->network)->flags & FLAG_USE_GLOBAL) &&
								 (((ircnet *)serv->network)->user)) ?
								(((ircnet *)serv->network)->user) :
								prefs.hex_irc_user_name,
								(!(((ircnet *)serv->network)->flags & FLAG_USE_GLOBAL) &&
								 (((ircnet *)serv->network)->real)) ?
								(((ircnet *)serv->network)->real) :
								prefs.hex_irc_real_name);
		} else
		{
			serv->p_login (serv, prefs.hex_irc_user_name, prefs.hex_irc_real_name);
		}
	} else
	{
		EMIT_SIGNAL (XP_TE_SERVERCONNECTED, serv->server_session, NULL, NULL,
						 NULL, NULL, 0);
	}

	server_set_name (serv, serv->servername);
	fe_server_event (serv, FE_SE_CONNECT, 0);
}

static void
server_stopconnecting (server * serv)
{
	if (serv->joindelay_tag)
	{
		fe_timeout_remove (serv->joindelay_tag);
		serv->joindelay_tag = 0;
	}

	fe_progressbar_end (serv);

	serv->connecting = FALSE;
	fe_server_event (serv, FE_SE_DISCONNECT, 0);
}

static int
timeout_auto_reconnect (server *serv)
{
	if (is_server (serv))  /* make sure it hasnt been closed during the delay */
	{
		serv->recondelay_tag = 0;
		if (!serv->connected && !serv->connecting && serv->server_session)
		{
			server_connect (serv, serv->hostname, serv->port, FALSE);
		}
	}
	return 0;			  /* returning 0 should remove the timeout handler */
}

static void
auto_reconnect (server *serv, int send_quit, char *err)
{
	session *s;
	GSList *list;
	int del;

	if (serv->server_session == NULL)
		return;

	list = sess_list;
	while (list)				  /* make sure auto rejoin can work */
	{
		s = list->data;
		if (s->type == SESS_CHANNEL && s->channel[0])
		{
			strcpy (s->waitchannel, s->channel);
			strcpy (s->willjoinchannel, s->channel);
		}
		list = list->next;
	}

	if (serv->connected)
		server_disconnect (serv->server_session, send_quit, err);

	del = prefs.hex_net_reconnect_delay * 1000;
	if (del < 1000)
		del = 500;				  /* so it doesn't block the gui */


	serv->reconnect_away = serv->is_away;

	/* is this server in a reconnect delay? remove it! */
	if (serv->recondelay_tag)
	{
		fe_timeout_remove (serv->recondelay_tag);
		serv->recondelay_tag = 0;
	}

	serv->recondelay_tag = fe_timeout_add (del, timeout_auto_reconnect, serv);
	fe_server_event (serv, FE_SE_RECONDELAY, del);
}

static void
server_flush_queue (server *serv)
{
	list_free (&serv->outbound_queue);
	serv->sendq_len = 0;
	fe_set_throttle (serv);
}

/* connect() successed */

static void
server_connect_success (server *serv)
{
	server_stopconnecting (serv);	/* ->connecting = FALSE */
	server_connected (serv);
}

/* Stop a connection attempt, or
   disconnect if already connected. */

static int
server_cleanup (server * serv)
{
	fe_set_lag (serv, 0);

	if (serv->joindelay_tag)
	{
		fe_timeout_remove (serv->joindelay_tag);
		serv->joindelay_tag = 0;
	}

	if (serv->connecting)
	{
		server_stopconnecting (serv);
		return 1;
	}

	if (serv->connected)
	{
		g_object_unref (serv->conn);
		serv->connected = FALSE;
		serv->end_of_motd = FALSE;
		return 2;
	}

	/* is this server in a reconnect delay? remove it! */
	if (serv->recondelay_tag)
	{
		fe_timeout_remove (serv->recondelay_tag);
		serv->recondelay_tag = 0;
		return 3;
	}

	return 0;
}

static void
server_disconnect (session * sess, int sendquit, char *err)
{
	server *serv = sess->server;
	GSList *list;
	gboolean shutup = FALSE;

	/* send our QUIT reason */
	if (sendquit && serv->connected)
	{
		server_sendquit (sess);
	}

	fe_server_event (serv, FE_SE_DISCONNECT, 0);

	/* close all sockets & io tags */
	switch (server_cleanup (serv))
	{
	case 0:							  /* it wasn't even connected! */
		notc_msg (sess);
		return;
	case 1:							  /* it was in the process of connecting */
		PrintTextf (sess, _("Stopping Connection"));
		return;
	case 3:
		shutup = TRUE;	/* won't print "disconnected" in channels */
	}

	server_flush_queue (serv);

	list = sess_list;
	while (list)
	{
		sess = (struct session *) list->data;
		if (sess->server == serv)
		{
			if (!shutup || sess->type == SESS_SERVER)
				/* print "Disconnected" to each window using this server */
				EMIT_SIGNAL (XP_TE_DISCON, sess, err, NULL, NULL, NULL, 0);

			if (!sess->channel[0] || sess->type == SESS_CHANNEL)
				clear_channel (sess);
		}
		list = list->next;
	}

	serv->pos = 0;
	serv->motd_skipped = FALSE;
	serv->no_login = FALSE;
	serv->servername[0] = 0;
	serv->lag_sent = 0;

	notify_cleanup ();
}

static void
server_event_cb (GSocketClient *client, GSocketClientEvent event,
				GSocketConnectable *connectable, GIOStream *conn, server *serv)
{
	session *sess;

	if (!is_server (serv))
	{
		g_object_unref (client);
		return;
	}
	if (!serv->connecting)
	{
		server_cleanup (serv);
		return;
	}

	sess = serv->server_session;

	switch (event)
	{
	case G_SOCKET_CLIENT_RESOLVING:
		/* FIXME: may be emitted multiple times */
		EMIT_SIGNAL (XP_TE_SERVERLOOKUP, sess, serv->hostname, NULL, NULL, NULL, 0);
		break;
	case G_SOCKET_CLIENT_PROXY_NEGOTIATING:
		PrintTextf (sess, "Negotiating proxy");
		break;
	case G_SOCKET_CLIENT_PROXY_NEGOTIATED:
		PrintTextf (sess, "Connected to proxy");
		break;
	case G_SOCKET_CLIENT_CONNECTING:
	{
#if GLIB_CHECK_VERSION (2, 40, 0)
		GInetSocketAddress *sock_addr;
		GInetAddress *inet_addr;
		gchar *addr;
		gchar port[6];

		sock_addr = G_INET_SOCKET_ADDRESS (
					g_socket_connection_get_remote_address (G_SOCKET_CONNECTION(conn), NULL));
		if (sock_addr)
		{
			inet_addr = g_inet_socket_address_get_address (sock_addr);
			addr = g_inet_address_to_string (inet_addr);
			g_snprintf (port, sizeof (port), "%d", g_inet_socket_address_get_port (sock_addr));

			EMIT_SIGNAL (XP_TE_CONNECT, sess, serv->hostname, addr, port, NULL, 0);

			g_object_unref (sock_addr);
			g_free (addr);
		}
#endif
		break;
	}
	case G_SOCKET_CLIENT_TLS_HANDSHAKING:
	{
		GTlsCertificate *cert;
		char *cert_file;
		serv->have_cert = FALSE;

		/* first try network specific cert/key */
		cert_file = g_strdup_printf ("%s" G_DIR_SEPARATOR_S "certs" G_DIR_SEPARATOR_S "%s.pem",
					 get_xdir (), server_get_network (serv, TRUE));
		if ((cert = g_tls_certificate_new_from_file (cert_file, NULL)))
		{
			g_tls_connection_set_certificate (G_TLS_CONNECTION(conn), cert);
			serv->have_cert = TRUE;
		}
		else
		{
			g_free (cert_file);
			/* if that doesn't exist, try <config>/certs/client.pem */
			cert_file = g_build_filename (get_xdir (), "certs", "client.pem", NULL);
			if ((cert = g_tls_certificate_new_from_file (cert_file, NULL)))
			{
				g_tls_connection_set_certificate (G_TLS_CONNECTION(conn), cert);
				serv->have_cert = TRUE;
			}
		}
		g_free (cert_file);
		break;
	}
	default:
		break;
	}
}

static void
server_connection_ready (GSocketClient *client, GAsyncResult *res, server *serv)
{
	GSocketConnection *conn;
	GError *error = NULL;
	gboolean failed = FALSE;
	gchar *error_msg = "";

	conn = g_socket_client_connect_to_host_finish (client, res, &error);
	if (!is_server(serv))
	{
		g_object_unref (client);
		return;
	}

	if (error)
	{
		session *sess = serv->server_session;
		error_msg = error->message;

		switch (error->code)
		{
		case 0: /* FIXME: Is this the actual error code? */
			EMIT_SIGNAL (XP_TE_UKNHOST, sess, NULL, NULL, NULL, NULL, 0);
			break;
		default:
			EMIT_SIGNAL (XP_TE_CONNFAIL, sess, error_msg, NULL, NULL, NULL, 0);
			break;
		}
		failed = TRUE;
	}

	if (!serv->connecting)
	{
		g_object_unref (client);
		server_cleanup (serv);
	}
	else if (failed)
	{
		g_object_unref (client);
		if (!servlist_cycle (serv) && prefs.hex_net_auto_reconnectonfail)
			auto_reconnect (serv, FALSE, error_msg);
		else
			server_stopconnecting (serv);
		
		if (error)
			g_error_free (error);
	}
	else
	{
		serv->conn = conn;
		server_connect_success (serv);
	}
}

static void
server_connect (server *serv, char *hostname, int port, int no_login)
{
	GSocketClient *client;
	session *sess = serv->server_session;

	if (!hostname[0])
		return;

	if (port < 0)
	{
		/* use default port for this server type */
		port = 6667;
		if (serv->use_ssl)
			port = 6697;
	}
	port &= 0xffff;	/* wrap around */

	if (serv->connected || serv->connecting || serv->recondelay_tag)
		server_disconnect (sess, TRUE, NULL);

	safe_strcpy (serv->servername, hostname, sizeof (serv->servername));
	/* overlap illegal in strncpy */
	if (hostname != serv->hostname)
		safe_strcpy (serv->hostname, hostname, sizeof (serv->hostname));

	server_set_defaults (serv);
	serv->connecting = TRUE;
	serv->port = port;
	serv->no_login = no_login;

	fe_progressbar_start (sess);
	fe_server_event (serv, FE_SE_CONNECTING, 0);
	fe_set_away (serv);
	server_flush_queue (serv);

	client = g_socket_client_new ();

	/* TLS */
	g_socket_client_set_tls (client, serv->use_ssl);
	if (serv->accept_invalid_cert)
	{
		GTlsCertificateFlags flags = 0;
		g_socket_client_set_tls_validation_flags (client, flags);
	}

	/* Proxy */
	if (!serv->dont_use_proxy && prefs.hex_net_proxy_use != 2)
	{
		GProxyResolver *proxy;
		gchar *proxy_uri;

		proxy_uri = hexchat_proxy_uri ();
		if (proxy_uri)
		{
			proxy = g_simple_proxy_resolver_new (proxy_uri, NULL);
			g_socket_client_set_proxy_resolver (client, proxy);
			g_socket_client_set_enable_proxy (client, TRUE);

			g_free (proxy_uri);
			g_object_unref (proxy);
		}
	}
	else
	{
		g_socket_client_set_enable_proxy (client, FALSE);
	}

	if (prefs.hex_net_bind_host && *prefs.hex_net_bind_host)
	{
		GSocketAddress *addr;

		/* TODO: Test this */
		addr = g_inet_socket_address_new_from_string (prefs.hex_net_bind_host, 0);
		if (addr)
			g_socket_client_set_local_address (client, addr);
		/* TODO: Set prefs.local_ip somewhere */
	}

	/* TODO: This setting is already used by lag_check, replace here? */
	g_socket_client_set_timeout (client, prefs.hex_net_ping_timeout);

	g_signal_connect (G_OBJECT(client), "event", G_CALLBACK(server_event_cb), serv);
	g_socket_client_connect_to_host_async (client, hostname, port, NULL,
							(GAsyncReadyCallback)server_connection_ready, serv);
}

void
server_fill_her_up (server *serv)
{
	serv->connect = server_connect;
	serv->disconnect = server_disconnect;
	serv->cleanup = server_cleanup;
	serv->flush_queue = server_flush_queue;
	serv->auto_reconnect = auto_reconnect;

	proto_fill_her_up (serv);
}

void
server_set_encoding (server *serv, char *new_encoding)
{
	char *space;

	if (serv->encoding)
	{
		free (serv->encoding);
		/* can be left as NULL to indicate system encoding */
		serv->encoding = NULL;
		serv->using_cp1255 = FALSE;
		serv->using_irc = FALSE;
	}

	if (new_encoding)
	{
		serv->encoding = strdup (new_encoding);
		/* the serverlist GUI might have added a space
			and short description - remove it. */
		space = strchr (serv->encoding, ' ');
		if (space)
			space[0] = 0;

		/* server_inline() uses these flags */
		if (!g_ascii_strcasecmp (serv->encoding, "CP1255") ||
			 !g_ascii_strcasecmp (serv->encoding, "WINDOWS-1255"))
			serv->using_cp1255 = TRUE;
		else if (!g_ascii_strcasecmp (serv->encoding, "IRC"))
			serv->using_irc = TRUE;
	}
}

server *
server_new (void)
{
	static int id = 0;
	server *serv;

	serv = malloc (sizeof (struct server));
	memset (serv, 0, sizeof (struct server));

	/* use server.c and proto-irc.c functions */
	server_fill_her_up (serv);

	serv->id = id++;
	strcpy (serv->nick, prefs.hex_irc_nick1);
	server_set_defaults (serv);

	serv_list = g_slist_prepend (serv_list, serv);

	fe_new_server (serv);

	return serv;
}

int
is_server (server *serv)
{
	return g_slist_find (serv_list, serv) ? 1 : 0;
}

void
server_set_defaults (server *serv)
{
	if (serv->chantypes)
		free (serv->chantypes);
	if (serv->chanmodes)
		free (serv->chanmodes);
	if (serv->nick_prefixes)
		free (serv->nick_prefixes);
	if (serv->nick_modes)
		free (serv->nick_modes);

	serv->chantypes = strdup ("#&!+");
	serv->chanmodes = strdup ("beI,k,l");
	serv->nick_prefixes = strdup ("@%+");
	serv->nick_modes = strdup ("ohv");

	serv->nickcount = 1;
	serv->end_of_motd = FALSE;
	serv->is_away = FALSE;
	serv->supports_watch = FALSE;
	serv->supports_monitor = FALSE;
	serv->bad_prefix = FALSE;
	serv->use_who = TRUE;
	serv->have_namesx = FALSE;
	serv->have_awaynotify = FALSE;
	serv->have_uhnames = FALSE;
	serv->have_whox = FALSE;
	serv->have_idmsg = FALSE;
	serv->have_accnotify = FALSE;
	serv->have_extjoin = FALSE;
	serv->have_server_time = FALSE;
	serv->have_sasl = FALSE;
	serv->have_except = FALSE;
	serv->have_invite = FALSE;
}

char *
server_get_network (server *serv, gboolean fallback)
{
	/* check the network list */
	if (serv->network)
		return ((ircnet *)serv->network)->name;

	/* check the network name given in 005 NETWORK=... */
	if (serv->server_session && *serv->server_session->channel)
		return serv->server_session->channel;

	if (fallback)
		return serv->servername;

	return NULL;
}

void
server_set_name (server *serv, char *name)
{
	GSList *list = sess_list;
	session *sess;

	if (name[0] == 0)
		name = serv->hostname;

	/* strncpy parameters must NOT overlap */
	if (name != serv->servername)
	{
		safe_strcpy (serv->servername, name, sizeof (serv->servername));
	}

	while (list)
	{
		sess = (session *) list->data;
		if (sess->server == serv)
			fe_set_title (sess);
		list = list->next;
	}

	if (serv->server_session->type == SESS_SERVER)
	{
		if (serv->network)
		{
			safe_strcpy (serv->server_session->channel, ((ircnet *)serv->network)->name, CHANLEN);
		} else
		{
			safe_strcpy (serv->server_session->channel, name, CHANLEN);
		}
		fe_set_channel (serv->server_session);
	}
}

struct away_msg *
server_away_find_message (server *serv, char *nick)
{
	struct away_msg *away;
	GSList *list = away_list;
	while (list)
	{
		away = (struct away_msg *) list->data;
		if (away->server == serv && !serv->p_cmp (nick, away->nick))
			return away;
		list = list->next;
	}
	return NULL;
}

static void
server_away_free_messages (server *serv)
{
	GSList *list, *next;
	struct away_msg *away;

	list = away_list;
	while (list)
	{
		away = list->data;
		next = list->next;
		if (away->server == serv)
		{
			away_list = g_slist_remove (away_list, away);
			if (away->message)
				free (away->message);
			free (away);
			next = away_list;
		}
		list = next;
	}
}

void
server_away_save_message (server *serv, char *nick, char *msg)
{
	struct away_msg *away = server_away_find_message (serv, nick);

	if (away)						  /* Change message for known user */
	{
		if (away->message)
			free (away->message);
		away->message = strdup (msg);
	} else
		/* Create brand new entry */
	{
		away = malloc (sizeof (struct away_msg));
		if (away)
		{
			away->server = serv;
			safe_strcpy (away->nick, nick, sizeof (away->nick));
			away->message = strdup (msg);
			away_list = g_slist_prepend (away_list, away);
		}
	}
}

void
server_free (server *serv)
{
	serv->cleanup (serv);

	serv_list = g_slist_remove (serv_list, serv);

	dcc_notify_kill (serv);
	serv->flush_queue (serv);
	server_away_free_messages (serv);

	free (serv->nick_modes);
	free (serv->nick_prefixes);
	free (serv->chanmodes);
	free (serv->chantypes);
	if (serv->bad_nick_prefixes)
		free (serv->bad_nick_prefixes);
	if (serv->last_away_reason)
		free (serv->last_away_reason);
	if (serv->encoding)
		free (serv->encoding);
	if (serv->favlist)
		g_slist_free_full (serv->favlist, (GDestroyNotify) servlist_favchan_free);

	fe_server_callback (serv);

	free (serv);

	notify_cleanup ();
}
