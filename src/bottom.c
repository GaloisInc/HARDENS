// HARDENS Reactor Trip System (RTS) "Bottom" Implementation
// In support of the formal assurance case for the RTS, as realized
// using Frama-C and SAW.

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

#include "actuate.h"
#include "actuation_logic.h"
#include "common.h"
#include "core.h"
#include "instrumentation.h"
#include "platform.h"
#include "sense_actuate.h"

#include <assert.h>

int actuate_devices(void) {
  assert(0);
  return 0;
}

uint8_t ActuateActuator(uint8_t vs) {
  assert(0);
  return 0;
}

uint8_t Coincidence_2_4(uint8_t trips[4]) {
  assert(0);
  return 0;
}

uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old) {
  assert(0);
  return 0;
}

uint8_t Actuate_D1(uint8_t trips[3][4], uint8_t old) {
  assert(0);
  return 0;
}

int actuation_unit_step(uint8_t logic_no, struct actuation_logic *state) {
  assert(0);
  return 0;
}

int sense_actuate_init(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation) {
  assert(0);
  return 0;
}

int sense_actuate_step_0(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation)

{
  assert(0);
  return 0;
}

int sense_actuate_step_1(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation) {
  assert(0);
  return 0;
}

void core_init(struct core_state *core) { assert(0); }

int core_step(struct core_state *core) {
  assert(0);
  return 0;
}

void instrumentation_init(struct instrumentation_state *state) { assert(0); }

int instrumentation_step(uint8_t div, struct instrumentation_state *state) {
  assert(0);
  return 0;
}
int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  assert(0);
  return 0;
}

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value) {
  assert(0);
  return 0;
}

int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value) {
  assert(0);
  return 0;
}

int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value) {
  assert(0);
  return 0;
}

int get_instrumentation_maintenance(uint8_t division, uint8_t *value) {
  assert(0);
  return 0;
}

int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value) {
  assert(0);
  return 0;
}

int read_instrumentation_trip_signals(uint8_t arr[3][4]) {
  assert(0);
  return 0;
}

int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no,
                               uint8_t on) {
  assert(0);
  return 0;
}

int set_output_instrumentation_trip(uint8_t division, uint8_t channel,
                                    uint8_t val) {
  assert(0);
  return 0;
}

int set_actuate_device(uint8_t device_no, uint8_t on) {
  assert(0);
  return 0;
}

int read_rts_command(struct rts_command *cmd) {
  assert(0);
  return 0;
}

int read_instrumentation_command(uint8_t division,
                                 struct instrumentation_command *cmd) {
  assert(0);
  return 0;
}

int send_instrumentation_command(uint8_t division,
                                 struct instrumentation_command *cmd) {
  assert(0);
  return 0;
}

int read_actuation_command(uint8_t id, struct actuation_command *cmd) {
  assert(0);
  return 0;
}

int send_actuation_command(uint8_t actuator, struct actuation_command *cmd) {
  assert(0);
  return 0;
}

int set_display_line(uint8_t line_number, const char *display, uint32_t size) {
  assert(0);
  return 0;
}

uint8_t is_test_running() {
  assert(0);
  return 0;
}

void set_test_running(int val) { assert(0); }

uint8_t get_test_device() {
  assert(0);
  return 0;
}

void get_test_instrumentation(uint8_t *id) { assert(0); }

int get_instrumentation_test_setpoints(uint8_t id, uint32_t *setpoints) {
  assert(0);
  return 0;
}
void set_instrumentation_test_complete(uint8_t div, int v) { assert(0); }
int is_instrumentation_test_complete(uint8_t id) {
  assert(0);
  return 0;
}
int read_test_instrumentation_channel(uint8_t div, uint8_t channel,
                                      uint32_t *val) {
  assert(0);
  return 0;
}

uint8_t get_test_actuation_unit() {
  assert(0);
  return 0;
}
int is_actuation_unit_under_test(uint8_t id) {
  assert(0);
  return 0;
}
void set_actuation_unit_test_complete(uint8_t div, int v) { assert(0); }
void set_actuation_unit_test_input_vote(uint8_t id, int v) { assert(0); }
int is_actuation_unit_test_complete(uint8_t id) {
  assert(0);
  return 0;
}

void set_actuate_test_result(uint8_t dev, uint8_t result) { assert(0); }
void set_actuate_test_complete(uint8_t dev, int v) { assert(0); }
int is_actuate_test_complete(uint8_t dev) {
  assert(0);
  return 0;
}

int main(int argc, char **argv) {
  assert(0);
  return 0;
}
