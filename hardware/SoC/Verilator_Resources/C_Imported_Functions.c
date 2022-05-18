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
#include <termios.h>
#include <unistd.h>
#include <sys/types.h>
#include <poll.h>
#include <sched.h>

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


// NOTE: Not needed right now
void print_tty(char* name, FILE * f) {
    printf("%s (fileno %d): ", name, fileno(f));
    if (isatty(fileno(f))) printf("TTY %s\n", ttyname(fileno(f)));
    else                   printf("not a TTY\n");
}

// TODO: set to 1 to try avoid line buffering
#define INIT_TERMIOS 0
uint8_t c_trygetchar (uint8_t  dummy)
{
    uint8_t  ch;
    ssize_t  n;
    struct pollfd  x_pollfd;
    const int fd_stdin = 0;

#if INIT_TERMIOS
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
#endif

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


/**
 * Assume that both sensors have 12 bit resolution
 * and two data registers
 *
 * Pressure sensor: https://cdn.sparkfun.com/datasheets/Sensors/Pressure/MPL3115A2.pdf#G1007342
 * Temp sensor: https://www.sparkfun.com/datasheets/Sensors/Temperature/tmp102.pdf
 *
 * TODO: simplify
 */
// channel -> sensor # -> val
uint32_t sensors[2][2];
uint8_t c_i2c_request (uint8_t slaveaddr, uint8_t data) {
    static uint8_t data_reg = 0;
    static uint8_t pointer_reg = 1;
    static int initialized = 0;
    static uint32_t last_update = 0;
    static uint32_t last[2][2] = {0};

    struct timespec tp;
    clock_gettime(CLOCK_REALTIME, &tp);
    uint32_t t = tp.tv_sec*1000 + tp.tv_nsec/1000000;

    if (!initialized) {
        last_update = t;
        last[0][T] = T0;
        last[1][T] = T0;
        last[0][P] = P0;
        last[1][P] = P0;
        sensors[0][T] = last[0][T];
        sensors[1][T] = last[1][T];
        sensors[0][P] = last[0][P];
        sensors[1][P] = last[1][P];
        initialized = 1;
    } else if (t - last_update > SENSOR_UPDATE_MS) {
        for (int s = 0; s < 2; ++s) {
            last[s][T] += (rand() % 3) - 1;
            // TODO: Temp sensor resolution is -25..85C
            // Don't stray too far from our steam table
            last[s][T] = min(last[s][T], 300);
            last[s][T] = max(last[s][T], 25);

            last[s][P] += (rand() % 3) - 1 + P_BIAS;
            // Don't stray too far from our steam table
            last[s][P] = min(last[s][P], 5775200);
            last[s][P] = max(last[s][P], 8000);
        }
        last_update = t;
    }
    // Smooth the transitions
    sensors[0][T] = last[0][T];
    sensors[1][T] = last[1][T];
    sensors[0][P] = last[0][P];
    sensors[1][P] = last[1][P];

    if (slaveaddr & 0x1) {
        // Write request
        pointer_reg = data % 4;
        data_reg = pointer_reg;
    } else {
        // Read request, use 7bit addressing
        uint8_t dev_addr = slaveaddr >> 1;
        switch (dev_addr) {
            case TEMP_0_I2C_ADDR:
                data_reg = (uint8_t)(sensors[0][T] >> pointer_reg*8);
                break;
            case TEMP_1_I2C_ADDR:
                data_reg = (uint8_t)(sensors[1][T] >> pointer_reg*8);
                break;
            case PRESSURE_0_I2C_ADDR:
                data_reg = (uint8_t)(sensors[0][P] >> pointer_reg*8);
                break;
            case PRESSURE_1_I2C_ADDR:
                data_reg = (uint8_t)(sensors[1][P] >> pointer_reg*8);
                break;
            default:
                data_reg = 0xAA;
                break;
        }

    }
    return data_reg;
}
