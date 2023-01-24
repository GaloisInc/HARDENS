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

#include "instrumentation.h"
#include "platform.h"
#include "common.h"
#include "core.h"
#include <string.h>

#define TRIP_I(_v, _i) (((_v) >> (_i)) & 0x1)

/*@requires div < NINSTR;
  @requires \valid(state);
  @requires \valid(state->reading + (0.. NTRIP-1));
  @requires \valid(state->test_reading + (0.. NTRIP-1));
  @requires \valid(state->setpoints + (0.. NTRIP-1));
  @requires \valid(state->sensor_trip + (0.. NTRIP-1));
  @assigns state->reading[0.. NTRIP-1];
  @assigns state->test_reading[0.. NTRIP-1];
  @assigns state->sensor_trip[0.. NTRIP-1];
  @ensures -1 <= \result <= 0;
*/
static int instrumentation_step_trip(uint8_t div,
                                     int do_test,
                                     struct instrumentation_state *state) {
  int err = 0;

  if (do_test) {
    err |= read_test_instrumentation_channel(div, T, &state->test_reading[T]);
    err |= read_test_instrumentation_channel(div, P, &state->test_reading[P]);
    state->test_reading[S] = Saturation(state->test_reading[T], state->test_reading[P]);
  } else {
    err |= read_instrumentation_channel(div, T, &state->reading[T]);
    err |= read_instrumentation_channel(div, P, &state->reading[P]);
    state->reading[S] = Saturation(state->reading[T], state->reading[P]);
  }

  uint8_t new_trips = 0;

  if (do_test) {
    uint32_t setpoints[3];
    err |= get_instrumentation_test_setpoints(div, &setpoints[0]);
    new_trips = Generate_Sensor_Trips(state->test_reading, setpoints);
  } else {
    new_trips = Generate_Sensor_Trips(state->reading, state->setpoints);
  }

  /*@loop invariant 0 <= i && i <= NTRIP;
    @loop assigns i;
    @loop assigns state->sensor_trip[0.. NTRIP-1];
  */
  for (int i = 0; i < NTRIP; ++i) {
    state->sensor_trip[i] = TRIP_I(new_trips, i);
  }

  return err;
}

/*@requires \valid(i_cmd);
  @requires \valid(state);
  @requires state->mode[0] \in {0,1,2};
  @requires state->mode[1] \in {0,1,2};
  @requires state->mode[2] \in {0,1,2};
  @assigns state->maintenance, state->mode[0..2], state->setpoints[0..2];
  @ensures -1 <= \result <= 0;
  @ensures state->mode[0] \in {0,1,2};
  @ensures state->mode[1] \in {0,1,2};
  @ensures state->mode[2] \in {0,1,2};
*/
static int instrumentation_handle_command(uint8_t div,
                                          struct instrumentation_command *i_cmd,
                                          struct instrumentation_state *state) {
  struct set_maintenance set_maint;
  struct set_mode set_mode;
  struct set_setpoint set_setpoint;

  switch (i_cmd->type) {
  case SET_MAINTENANCE:
    set_maint = i_cmd->cmd.maintenance;
    state->maintenance = set_maint.on;
    break;

  case SET_MODE:
    set_mode = i_cmd->cmd.mode;
    if (state->maintenance && set_mode.channel < NTRIP &&
        set_mode.mode_val < NMODES) {
      state->mode[set_mode.channel] = set_mode.mode_val;
    }
    break;

  case SET_SETPOINT:
    set_setpoint = i_cmd->cmd.setpoint;
    if (state->maintenance && set_setpoint.channel < NTRIP) {
      state->setpoints[set_setpoint.channel] = set_setpoint.val;
    }
    break;

  default:
    return -1;
  }

  return 0;
}

/*@ requires div < NINSTR;
  @ requires \valid(state);
  @ requires state->mode[0] \in {0,1,2};
  @ requires state->mode[1] \in {0,1,2};
  @ requires state->mode[2] \in {0,1,2};
  @ assigns core.test.test_instrumentation_done[div];
  @ ensures \result <= 0;
*/
static int instrumentation_set_output_trips(uint8_t div,
                                            int do_test,
                                            struct instrumentation_state *state)
{
  /*@ loop invariant 0 <= i <= NTRIP;
    @ loop assigns i;
  */
  for (int i = 0; i < NTRIP; ++i) {
    uint8_t mode = do_test ? 1 : state->mode[i];
    set_output_instrumentation_trip(div, i, BIT(do_test, Is_Ch_Tripped(mode, 0 != state->sensor_trip[i])));
  }

  if (do_test) {
    set_instrumentation_test_complete(div, 1);
  }

  return 0;
}

int instrumentation_step(uint8_t div, struct instrumentation_state *state) {
  int err = 0;

  uint8_t test_div[2];
  get_test_instrumentation(test_div);
  int do_test = (div == test_div[0] || div == test_div[1]) && is_test_running();

  if (do_test && is_instrumentation_test_complete(div))
    return 0;

  if (!do_test && is_instrumentation_test_complete(div)) {
    set_instrumentation_test_complete(div, 0);
  }

  /* Read trip signals & vote */
  err |= instrumentation_step_trip(div, do_test, state);

  /* Handle any external commands */
  struct instrumentation_command i_cmd;
  int read_cmd = read_instrumentation_command(div, &i_cmd);
  if (read_cmd > 0) {
    err |= instrumentation_handle_command(div, &i_cmd, state);
  } else if (read_cmd < 0) {
    err |= -read_cmd;
  }

  /* Actuate devices based on voting and commands */
  err |= instrumentation_set_output_trips(div, do_test, state);
  return err;
}
