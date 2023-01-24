// HARDENS Reactor Trip System (RTS)

// Copyright 2021, 2022, 2023 Galois, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#ifndef COMMON_H_
#define COMMON_H_

#include <stdint.h>

//////////////////////////////////////////////////////////////
// Constants derived from architecture and Cryptol model    //
//////////////////////////////////////////////////////////////

// Instrumentation
// Trip modes:
#define NINSTR 4
#define NMODES 3
#define BYPASS 0
#define OPERATE 1
#define TRIP 2

// Command Types
#define SET_MODE 0
#define SET_MAINTENANCE 1
#define SET_SETPOINT 2

// Channel/Trip signal IDs
#define NTRIP 3
#define T 0
#define P 1
#define S 2

// Actuation
#define NVOTE_LOGIC 2
#define NDEV 2

// Core
// Command Types
#define INSTRUMENTATION_COMMAND 0
#define ACTUATION_COMMAND 1

#define BIT(_test, _value) ((_test) ? (0x8 | (_value)) : _value)
#define VALID(_value) (!(0x8 & (_value)))
#define VAL(_value) (0x1 & value)

#define NLINES 21
#define LINELENGTH 64
//////////////////////////////////////////////////////////////
// RTS Command Definitions                                  //
//////////////////////////////////////////////////////////////

// Instrumentation
struct set_mode {
  uint8_t channel;
  uint8_t mode_val;
};
struct set_maintenance {
  uint8_t on;
};
struct set_setpoint {
  uint8_t channel;
  uint32_t val;
};
struct instrumentation_command {
  uint8_t type;
  uint8_t valid;
  union {
    struct set_mode mode;
    struct set_maintenance maintenance;
    struct set_setpoint setpoint;
  } cmd;
};

// Actuation
struct actuation_command {
    uint8_t device;
    uint8_t on;
};

// Root command structure
struct rts_command {
  uint8_t type;
  uint8_t instrumentation_division;
  union {
    struct instrumentation_command instrumentation;
    struct actuation_command act;
  } cmd;
};

// Redefine variable bit-width types:
#define _ExtInt_1 char
#define _ExtInt_2 char
#define _ExtInt_3 char
#define _ExtInt_4 char
#define _ExtInt_6 char
#define _ExtInt_8 char
#define _ExtInt_32 int
#define _ExtInt(w) _ExtInt_##w

// Generate names for implementation variants
#define VARIANT(source,lang,f) VARIANT_IMPL(source,lang,f)
#define VARIANT_IMPL(source,lang,f) f ## _ ## source ## _ ## lang
#define VARIANT_IMPL2(source,lang,f) source ## lang ## f

#endif // COMMON_H_
