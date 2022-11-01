// Copyright (c) 2016-2019 Bluespec, Inc.  All Rights Reserved
// Source: https://github.com/bluespec/Piccolo/blob/master/src_Testbench/Top/C_Imported_Functions.h
// Modified by @podhrmic

#pragma once

// ================================================================
// These are functions imported into BSV during Bluesim or Verilog simulation.
// See C_Imports.bsv for the corresponding 'import BDPI' declarations.

// There are several independent groups of functions below; the
// groups are separated by heavy dividers ('// *******')

// Below, 'dummy' args are not used, and are present only to appease
// some Verilog simulators that are finicky about 0-arg functions.

// ================================================================

#ifdef __cplusplus
extern "C" {
#endif

#include "../firmware/sensors.h"

// Channel/Trip signal IDs
#define NTRIP 3
#define T 0
#define P 1

// Min max values for sensors
// TODO @podhrmic fill with realistic values for ambient room temperature
#define TEMPERATURE_MIN_C 0 // for simplicity, assume no negative temps
#define TEMPERATURE_MAX_C 85
#define PRESSURE_MIN_P 8000
#define PRESSURE_MAX_P 60200 // we have 16bits at most

#define min(_a, _b) ((_a) < (_b) ? (_a) : (_b))
#define max(_a, _b) ((_a) > (_b) ? (_a) : (_b))


#ifndef T0
#define T0 200
#endif

#ifndef P0
#define P0 1152600
#endif

// Bias to simulated sensor readings in degrees F
#ifndef T_BIAS
#define T_BIAS 0
#endif

// Bias to simulated sensor readings in 10^-5 lb/in2
#ifndef P_BIAS
#define P_BIAS 0
#endif

#ifndef SENSOR_UPDATE_MS
#define SENSOR_UPDATE_MS 60000
#endif

// Functions for I/O

// ================================================================
// c_trygetchar()
// Returns next input character (ASCII code) from the console.
// Returns 0 if no input is available.

extern
uint8_t c_trygetchar (uint8_t  dummy);

// ================================================================
// c_putchar()
// Writes character to stdout

extern
void c_putchar (uint8_t ch);

extern
uint8_t c_i2c_request (uint8_t slaveaddr, uint8_t data);

// ****************************************************************
// ****************************************************************
// ****************************************************************

#ifdef __cplusplus
}

#endif
