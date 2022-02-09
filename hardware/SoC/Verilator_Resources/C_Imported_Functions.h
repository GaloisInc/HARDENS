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

// Functions for console I/O

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

// ****************************************************************
// ****************************************************************
// ****************************************************************

#ifdef __cplusplus
}
#endif
