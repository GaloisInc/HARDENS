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

#ifndef SENSE_ACTUATE_H_
#define SENSE_ACTUATE_H_

#include "common.h"
#include "instrumentation.h"
#include "actuation_logic.h"

/* Initialize state for core `core_id`.
 * @requires instrumentation is an array of NINSTRUMENTATION/NCORE_ID instrumentation structs
 * @requires actuation_logic is an array of NACTUATION_LOGIC/NCORE_ID actuation_logic structs
 * @returns < 0 on error
 */
int sense_actuate_init(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation);

/* Advance state for core `core_id`.
 * @requires instrumentation is an array of NINSTRUMENTATION/NCORE_ID instrumentation structs
 * @requires actuation_logic is an array of NACTUATION_LOGIC/NCORE_ID actuation_logic structs
 * @returns < 0 on error
 */
int sense_actuate_step_0(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation);
int sense_actuate_step_1(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation);

#endif // SENSE_ACTUATE_H_
