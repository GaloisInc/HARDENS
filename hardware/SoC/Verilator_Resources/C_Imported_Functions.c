// Copyright (c) 2013-2019 Bluespec, Inc.  All Rights Reserved
// https://github.com/bluespec/Piccolo/blob/master/src_Testbench/Top/C_Imported_Functions.c
// Modified by @podhrmic

// ================================================================
// These are functions imported into BSV during Bluesim or Verilog simulation.
// See C_Imports.bsv for the corresponding 'import BDPI' declarations.

// There are several independent groups of functions below; the
// groups are separated by heavy dividers ('// *******')

// Below, 'dummy' args are not used, and are present only to appease
// some Verilog simulators that are finicky about 0-arg functions.

// ================================================================
// Includes from C library

// General
#include <unistd.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <string.h>
#include <errno.h>
#include <time.h>

// For comms polling
#include <sys/types.h>
#include <poll.h>
#include <sched.h>

// For TCP
#include <sys/socket.h>       //  socket definitions
#include <sys/types.h>        //  socket types
#include <arpa/inet.h>        //  inet (3) funtions
#include <netinet/in.h>
#include <fcntl.h>            // To set non-blocking mode


// ================================================================
// Includes for this project

#include "C_Imported_Functions.h"

// ****************************************************************
// ****************************************************************
// ****************************************************************

// Functions for console I/O

// ================================================================
// c_trygetchar()
// Returns next input character (ASCII code) from the console.
// Returns 0 if no input is available.

#include <termios.h>
#include <unistd.h>

void print_tty(char* name, FILE * f) {
	printf("%s (fileno %d): ", name, fileno(f));
	if (isatty(fileno(f))) printf("TTY %s\n", ttyname(fileno(f)));
	else                   printf("not a TTY\n");
}

uint8_t c_trygetchar (uint8_t  dummy)
{
    uint8_t  ch;
    ssize_t  n;
    struct pollfd  x_pollfd;
    const int fd_stdin = 0;

	static bool init = false;
	if (!init) {
		print_tty("stdin ", stdin);
		print_tty("stdout", stdout);
		print_tty("stderr", stderr);

		struct termios tconf;

		// get original cooked/canonical mode values
		tcgetattr(fd_stdin,&tconf);

		// set options for raw mode
		tconf.c_lflag &= ~(ECHO | ICANON);       /* no echo or edit */
		tconf.c_cc[VMIN] = 0;
		tconf.c_cc[VTIME] = 0;

		// put unit into raw mode ...
    	tcsetattr(fd_stdin,TCSANOW,&tconf);
		printf("Terminal set to ~(ECHO | ICANON) mode\n");
		init = true;
	}

    // ----------------
    // Poll for input
    x_pollfd.fd      = fd_stdin;
    x_pollfd.events  = POLLRDNORM;
    x_pollfd.revents = 0;
    poll (& x_pollfd, 1, 1);

    //printf ("INFO: c_trygetchar: Polling for input\n");
    if ((x_pollfd.revents & POLLRDNORM) == 0) {
		//printf ("INFO: No input\n");
		return 0;
    }

    // ----------------
    // Input is available

    n = read (fd_stdin, & ch, 1);
    if (n == 1) {
		//printf ("INFO: got %c\n",ch);
	return ch;
    }
    else {
	if (n == 0)
	    printf ("c_trygetchar: end of file\n");
	return 0xFF;
    }
}

// ================================================================
// c_putchar()
// Writes character to stdout

void c_putchar (uint8_t ch)
{
	printf("%c",ch);
}

uint8_t c_i2c_request (uint8_t slaveaddr, uint8_t data) {
	// TODO: make this proper
	printf("Got i2c request, addr = 0x%X\n", slaveaddr);
	return data;
}
