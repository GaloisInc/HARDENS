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

#include "common.h"
#include "platform.h"
#include "instrumentation.h"
#include "actuation_logic.h"
#include "sense_actuate.h"

#ifdef PLATFORM_HOST
#include <stdio.h>
#else
#include "printf.h"
#endif

int instrumentation_step_generated_C(uint8_t div, struct instrumentation_state *state);
int instrumentation_step_handwritten_C(uint8_t div, struct instrumentation_state *state);
int instrumentation_step_generated_SystemVerilog(uint8_t div, struct instrumentation_state *state);
int instrumentation_step_handwritten_SystemVerilog(uint8_t div, struct instrumentation_state *state);
int actuation_unit_step_generated_C(uint8_t logic_no, struct actuation_logic *state);
int actuation_unit_step_generated_SystemVerilog(uint8_t logic_no, struct actuation_logic *state);

int sense_actuate_init(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation)
{
  DEBUG_PRINTF(("<sense_actuate.c> sense_actuate_init\n"));
  instrumentation_init(&instrumentation[0]);
  instrumentation_init(&instrumentation[1]);
  actuation->vote_actuate[0] = 0;
  actuation->vote_actuate[1] = 0;
  return 0;
}

int sense_actuate_step_0(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation)
{
  int err = 0;
  err |= instrumentation_step_generated_C(0,&instrumentation[0]);
  err |= instrumentation_step_handwritten_C(1,&instrumentation[1]);
  // Do we think the devices should be actuated?
  err |= actuation_unit_step_generated_C(0,actuation);
  DEBUG_PRINTF(("<sense_actuate.c> sense_actuate_step_0, err=0x%X\n",err));
  return err;
}

int sense_actuate_step_1(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation)
{
  int err = 0;
  err |= instrumentation_step_handwritten_SystemVerilog(2,&instrumentation[0]);
  err |= instrumentation_step_generated_SystemVerilog(3,&instrumentation[1]);
  // Do we think the devices should be actuated?
  err |= actuation_unit_step_generated_SystemVerilog(1,actuation);
  DEBUG_PRINTF(("<sense_actuate.c> sense_actuate_step_1, err=0x%X\n",err));
  return err;
}
