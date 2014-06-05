/* X-Chat
 * Copyright (C) 2001 Peter Zelezny.
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
 */

/* ipv4 and ipv6 networking functions with a common interface */

#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <glib.h>

#ifndef WIN32
#include <unistd.h>
#endif
#include "../../config.h"

#define WANTSOCKET
#define WANTARPA
#define WANTDNS
#include "inet.h"

#define NETWORK_PRIVATE
#include "network.h"

#define RAND_INT(n) ((int)(rand() / (RAND_MAX + 1.0) * (n)))


/* ================== COMMON ================= */

static void
net_set_socket_options (int sok)
{
	socklen_t sw;

	sw = 1;
	setsockopt (sok, SOL_SOCKET, SO_REUSEADDR, (char *) &sw, sizeof (sw));
	sw = 1;
	setsockopt (sok, SOL_SOCKET, SO_KEEPALIVE, (char *) &sw, sizeof (sw));
}

char *
net_ip (guint32 addr)
{
	struct in_addr ia;

	ia.s_addr = htonl (addr);
	return inet_ntoa (ia);
}

void
net_store_destroy (netstore * ns)
{
	if (ns->ip6_hostent)
		freeaddrinfo (ns->ip6_hostent);
	free (ns);
}

netstore *
net_store_new (void)
{
	netstore *ns;

	ns = malloc (sizeof (netstore));
	memset (ns, 0, sizeof (netstore));

	return ns;
}

char *
net_resolve (netstore * ns, char *hostname, int port, char **real_host)
{
	struct addrinfo hints;
	char ipstring[MAX_HOSTNAME];
	char portstring[MAX_HOSTNAME];
	int ret;

/*	if (ns->ip6_hostent)
		freeaddrinfo (ns->ip6_hostent);*/

	sprintf (portstring, "%d", port);

	memset (&hints, 0, sizeof (struct addrinfo));
	hints.ai_family = PF_UNSPEC; /* support ipv6 and ipv4 */
	hints.ai_flags = AI_CANONNAME | AI_ADDRCONFIG;
	hints.ai_socktype = SOCK_STREAM;

	if (port == 0)
		ret = getaddrinfo (hostname, NULL, &hints, &ns->ip6_hostent);
	else
		ret = getaddrinfo (hostname, portstring, &hints, &ns->ip6_hostent);
	if (ret != 0)
		return NULL;

#ifdef LOOKUPD	/* See note about lookupd above the IPv4 version of net_resolve. */
	struct addrinfo *tmp;
	int count = 0;

	for (tmp = ns->ip6_hostent; tmp; tmp = tmp->ai_next)
		count ++;

	count = RAND_INT(count);
	
	while (count--) ns->ip6_hostent = ns->ip6_hostent->ai_next;
#endif

	/* find the numeric IP number */
	ipstring[0] = 0;
	getnameinfo (ns->ip6_hostent->ai_addr, ns->ip6_hostent->ai_addrlen,
					 ipstring, sizeof (ipstring), NULL, 0, NI_NUMERICHOST);

	if (ns->ip6_hostent->ai_canonname)
		*real_host = strdup (ns->ip6_hostent->ai_canonname);
	else
		*real_host = strdup (hostname);

	return strdup (ipstring);
}

/* the only thing making this interface unclean, this shitty sok4, sok6 business */

int
net_connect (netstore * ns, int sok4, int sok6, int *sok_return)
{
	struct addrinfo *res, *res0;
	int error = -1;

	res0 = ns->ip6_hostent;

	for (res = res0; res; res = res->ai_next)
	{
/*		sok = socket (res->ai_family, res->ai_socktype, res->ai_protocol);
		if (sok < 0)
			continue;*/
		switch (res->ai_family)
		{
		case AF_INET:
			error = connect (sok4, res->ai_addr, res->ai_addrlen);
			*sok_return = sok4;
			break;
		case AF_INET6:
			error = connect (sok6, res->ai_addr, res->ai_addrlen);
			*sok_return = sok6;
			break;
		default:
			error = 1;
		}

		if (error == 0)
			break;
	}

	return error;
}

void
net_bind (netstore * tobindto, int sok4, int sok6)
{
	bind (sok4, tobindto->ip6_hostent->ai_addr,
			tobindto->ip6_hostent->ai_addrlen);
	bind (sok6, tobindto->ip6_hostent->ai_addr,
			tobindto->ip6_hostent->ai_addrlen);
}

void
net_sockets (int *sok4, int *sok6)
{
	*sok4 = socket (AF_INET, SOCK_STREAM, IPPROTO_TCP);
	*sok6 = socket (AF_INET6, SOCK_STREAM, IPPROTO_TCP);
	net_set_socket_options (*sok4);
	net_set_socket_options (*sok6);
}

void
udp_sockets (int *sok4, int *sok6)
{
	*sok4 = socket (AF_INET, SOCK_DGRAM, IPPROTO_UDP);
	*sok6 = socket (AF_INET6, SOCK_DGRAM, IPPROTO_UDP);
}

/* the following functions are used only by MSPROXY and are not
   proper ipv6 implementations - do not use in new code! */

void
net_store_fill_any (netstore *ns)
{
	struct addrinfo *ai;
	struct sockaddr_in *sin;

	ai = ns->ip6_hostent;
	if (!ai) {
		ai = malloc (sizeof (struct addrinfo));
		memset (ai, 0, sizeof (struct addrinfo));
		ns->ip6_hostent = ai;
	}
	sin = (struct sockaddr_in *)ai->ai_addr;
	if (!sin) {
		sin = malloc (sizeof (struct sockaddr_in));
		memset (sin, 0, sizeof (struct sockaddr_in));
		ai->ai_addr = (struct sockaddr *)sin;
	}
	ai->ai_family = AF_INET;
	ai->ai_addrlen = sizeof(struct sockaddr_in);
	sin->sin_family = AF_INET;
	sin->sin_addr.s_addr = INADDR_ANY;
	sin->sin_port = 0;
	ai->ai_next = NULL;
}

void
net_store_fill_v4 (netstore *ns, guint32 addr, int port)
{
	struct addrinfo *ai;
	struct sockaddr_in *sin;

	ai = ns->ip6_hostent;
	if (!ai) {
		ai = malloc (sizeof (struct addrinfo));
		memset (ai, 0, sizeof (struct addrinfo));
		ns->ip6_hostent = ai;
	}
	sin = (struct sockaddr_in *)ai->ai_addr;
	if (!sin) {
		sin = malloc (sizeof (struct sockaddr_in));
		memset (sin, 0, sizeof (struct sockaddr_in));
		ai->ai_addr = (struct sockaddr *)sin;
	}
	ai->ai_family = AF_INET;
	ai->ai_addrlen = sizeof(struct sockaddr_in);
	sin->sin_family = AF_INET;
	sin->sin_addr.s_addr = addr;
	sin->sin_port = port;
	ai->ai_next = NULL;
}

guint32
net_getsockaddr_v4 (netstore *ns)
{
	struct addrinfo *ai;
	struct sockaddr_in *sin;

	ai = ns->ip6_hostent;

	while (ai->ai_family != AF_INET) {
		ai = ai->ai_next;
		if (!ai)
			return 0;
	}
	sin = (struct sockaddr_in *)ai->ai_addr;
	return sin->sin_addr.s_addr;
}

int
net_getsockport (int sok4, int sok6)
{
	struct sockaddr_in addr;
	int len = sizeof (addr);

	if (getsockname (sok4, (struct sockaddr *)&addr, &len) == -1)
		return -1;
	return addr.sin_port;
}
