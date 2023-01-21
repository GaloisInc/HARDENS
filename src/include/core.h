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

#ifndef CORE_H_
#define CORE_H_

#include "common.h"

#ifndef SELF_TEST_PERIOD_SEC
#define SELF_TEST_PERIOD_SEC 20
#endif

#define NDIVISIONS 4

#ifndef T_THRESHOLD // degrees F
#define T_THRESHOLD 3
#endif

#ifndef P_THRESHOLD // 10^-5 lb/in^2
#define P_THRESHOLD 100
#endif

struct ui_values {
  uint32_t values[NDIVISIONS][NTRIP];
  uint8_t bypass[NDIVISIONS][NTRIP];
  uint8_t trip[NDIVISIONS][NTRIP];
  uint8_t maintenance[NDIVISIONS];
  char display[NLINES][LINELENGTH+1];

  uint8_t actuators[2][NDEV];
};

struct test_state {
  uint32_t test;
  uint32_t test_timer_start;
  uint8_t self_test_running;
  uint8_t self_test_expect;
  uint8_t failed;

  uint8_t test_device_result[2];

  uint8_t test_instrumentation[2];
  uint8_t test_actuation_unit;
  uint8_t test_device;

  uint8_t test_instrumentation_done[4];
  uint8_t test_actuation_unit_done[2];
  uint8_t test_device_done[2];

  uint32_t test_setpoints[4][3];
  uint32_t test_inputs[4][2];

  uint8_t actuation_old_vote;
};

struct core_state {
  struct ui_values ui;
  struct test_state test;
  uint8_t error;
};

extern struct core_state core;

int set_display_line(struct ui_values *ui, uint8_t line_number, char *display, uint32_t size);

void core_init(struct core_state *core);
int core_step(struct core_state *core);
#endif // CORE_H_
