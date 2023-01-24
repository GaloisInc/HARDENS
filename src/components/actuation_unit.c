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
#include "actuation_logic.h"

#ifdef PLATFORM_HOST
#include <stdio.h>
#else
#include "printf.h"
#endif

#define VOTE_I(_v, _i) (((_v) >> (_i)) & 0x1)

/*@requires \valid(&trip[0..2][0..3]);
  @requires \valid(&trip_test[0..2][0..3]);
  @assigns (trip[0..2][0..3]);
  @assigns (trip_test[0..2][0..3]);
*/
static int
actuation_logic_collect_trips(uint8_t logic_no, int do_test, uint8_t trip[3][4], uint8_t trip_test[3][4])
{
    int err = 0;
    uint8_t test_div[2];
    get_test_instrumentation(test_div);

    err |= read_instrumentation_trip_signals(trip);

    /*@ loop invariant 0 <= i <= NINSTR;
      @ loop assigns i;
      @ loop assigns trip[0..2][0..3];
      @ loop assigns trip_test[0..2][0..3];
    */
    for (int i = 0; i < NINSTR; ++i) {
        /*@ loop invariant 0 <= c <= NTRIP;
          @ loop assigns c;
          @ loop assigns trip[0..2][i];
          @ loop assigns trip_test[0..2][i];
        */
        for(int c = 0; c < NTRIP; ++c) {
            uint8_t test_signal = (i == test_div[0] || i == test_div[1]);
            if (do_test) {
                trip_test[c][i] = (trip[c][i] & test_signal) != 0;
                trip[c][i] &= !test_signal;
            } else if (!VALID(trip[c][i])) {
                trip[c][i] = 0;
            }
        }
    }

    return err;
}


/*@ requires \valid(&trips[0..2][0..3]);
  @ requires \valid(trips + (0..2));
  @ assigns \nothing;
*/
static uint8_t
actuate_device(uint8_t device, uint8_t trips[3][4], int old)
{
    uint8_t res = 0;
    if (device == 0) {
        res = Actuate_D0(trips, old);
    } else {
        res = Actuate_D1(trips, old);
    }
    DEBUG_PRINTF(("<actuation_unit.c> actuate_device: device=0x%X, old=0x%X, out=0x%X,trips=[\n", device, old, res));
    /*@ loop assigns i; */
    for (int i = 0; i < 3; ++i) {
        DEBUG_PRINTF(("["));
        /*@ loop assigns div; */
        for (int div = 0; div < 4; ++div) {
        DEBUG_PRINTF(("%u,",trips[i][div]));
        }
        DEBUG_PRINTF(("],"));
    }
    DEBUG_PRINTF(("]\n"));
    return res;
}

/*@requires \valid(state);
  @requires logic_no < NVOTE_LOGIC;
  @requires device < NDEV;
  @requires \valid(trip + (0..2));
  @requires \valid(trip_test + (0..2));
  @requires \valid(&trip[0..2][0..3]);
  @requires \valid(&trip_test[0..2][0..3]);
  @assigns state->vote_actuate[device];
  @assigns core.test.actuation_old_vote;
  @assigns core.test.test_actuation_unit_done[logic_no];
*/
static void
actuation_logic_vote_trips(uint8_t logic_no, int do_test, uint8_t device, uint8_t trip[3][4], uint8_t trip_test[3][4], struct actuation_logic *state)
{
    if (do_test && get_test_device() == device) {
        if (!is_actuation_unit_test_complete(logic_no)) {
            set_actuation_unit_test_input_vote(logic_no, state->vote_actuate[device] != 0);
            state->vote_actuate[device] = actuate_device(device, trip_test, state->vote_actuate[device] != 0);
        }
    } else {
        state->vote_actuate[device] = actuate_device(device, trip, state->vote_actuate[device] != 0);
    }
}

/*@ requires logic_no < NVOTE_LOGIC;
  @ requires \valid(state);
  @ assigns state->vote_actuate[0..1];

  @ assigns core.test.actuation_old_vote;
  @ assigns core.test.test_actuation_unit_done[logic_no];
*/
static int
actuation_logic_vote(uint8_t logic_no, int do_test, struct actuation_logic *state)
{
    int err = 0;
    uint8_t trip[3][4];
    uint8_t trip_test[3][4];

    err = actuation_logic_collect_trips(logic_no, do_test, trip, trip_test);

    actuation_logic_vote_trips(logic_no, do_test, 0, trip, trip_test, state);
    actuation_logic_vote_trips(logic_no, do_test, 1, trip, trip_test, state);

    return err;
}


/*@requires \valid(cmd);
  @requires \valid(state);
  @assigns state->manual_actuate[0..1];
  @ensures -1 <= \result <= 0;
*/
static int
actuation_handle_command(uint8_t logic_no, struct actuation_command *cmd, struct actuation_logic *state)
{
    if (cmd->device <= 1)
        state->manual_actuate[cmd->device] = cmd->on;
    return 0;
}

/*@requires \valid(state);
  @requires logic_no < NVOTE_LOGIC;
  @assigns state->vote_actuate[0..1];
  @assigns core.test.test_actuation_unit_done[logic_no];
  @ensures -1 <= \result <= 0;
*/
static int
output_actuation_signals(uint8_t logic_no, int do_test, struct actuation_logic *state)
{
    int err = 0;

    /*@ loop invariant 0 <= d <= NDEV;
      @ loop invariant -1 <= err <= 0;
      @ loop assigns d, err;
    */
    for (int d = 0; d < NDEV; ++d) {
        uint8_t on = state->vote_actuate[d] || state->manual_actuate[d];
        if (!do_test || !is_actuation_unit_test_complete(logic_no)) {
            err |= set_output_actuation_logic(logic_no, d, BIT(do_test, on));
        }
    }
    if (do_test && !is_actuation_unit_test_complete(logic_no)) {
        // Reset internal state
        state->vote_actuate[0] = 0;
        state->vote_actuate[1] = 0;
        set_actuation_unit_test_complete(logic_no, 1);
    }

    return err;
}

int actuation_unit_step(uint8_t logic_no, struct actuation_logic *state)
{
    int err = 0;
    uint8_t test_div[2];

    get_test_instrumentation(test_div);
    int do_test = logic_no == get_test_actuation_unit() &&
                  is_instrumentation_test_complete(test_div[0]) &&
                  is_instrumentation_test_complete(test_div[1]) &&
                  is_test_running();

    if (do_test && is_actuation_unit_test_complete(logic_no))
        return 0;

    if (!do_test && is_actuation_unit_test_complete(logic_no)) {
        set_output_actuation_logic(logic_no, get_test_device(), 0);
        set_actuation_unit_test_complete(logic_no, 0);
        return 0;
    }

    /* Read trip signals & vote */
    err |= actuation_logic_vote(logic_no, do_test, state);

    /* Handle any external commands */
    struct actuation_command cmd;
    int read_cmd = read_actuation_command(logic_no, &cmd);
    if (read_cmd > 0) {
        err |= actuation_handle_command(logic_no, &cmd, state);
    } else if (read_cmd < 0) {
        err |= -read_cmd;
    }

    /* Actuate devices based on voting and commands */
    err |= output_actuation_signals(logic_no, do_test, state);
    return err;
}
