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

#ifndef ACTUATION_H_
#define ACTUATION_H_

#include "stdint.h"
#include "common.h"
#include "instrumentation.h"
#include "core.h"
#include "models.acsl"

/*@requires \valid(&trips[0.. NINSTR -1]);
  @assigns \nothing;
  @ensures (\result != 0) <==> Coincidence_2_4(trips);
*/
uint8_t Coincidence_2_4(uint8_t trips[4]);

/*@requires \valid(&trips[0.. NTRIP - 1][0.. NINSTR - 1]);
  @requires \valid(trips + (0.. NTRIP-1));
  @assigns \nothing;
  @ensures (\result != 0) <==> Actuate_D0(&trips[T][0], &trips[P][0], &trips[S][0], old != 0);
*/
uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old);

/*@requires \valid(&trips[0.. NTRIP-1][0.. NINSTR-1]);
  @requires \valid(trips + (0.. NTRIP-1));
  @assigns \nothing;
  @ensures (\result != 0) <==> Actuate_D1(&trips[T][0], &trips[P][0], &trips[S][0], old != 0);
*/
uint8_t Actuate_D1(uint8_t trips[3][4], uint8_t old);

struct actuation_logic {
    uint8_t vote_actuate[NDEV];
    uint8_t manual_actuate[NDEV];
};

extern struct actuation_logic actuation_logic[2];

/* The main logic of the actuation unit */

/*@requires \valid(state);
  @requires logic_no <= 1;
  @assigns state->manual_actuate[0.. NDEV-1];
  @assigns state->vote_actuate[0.. NDEV-1];
  @assigns core.test.actuation_old_vote;
  @assigns core.test.test_actuation_unit_done[logic_no];
*/
int actuation_unit_step(uint8_t logic_no, struct actuation_logic *state);

#endif // ACTUATION_H_
