#ifndef CORE_H_
#define CORE_H_

#include "common.h"
#include "instrumentation.h"
#include "actuation_logic.h"

#define NDIVISIONS 4

struct ui_values {
  uint32_t values[NDIVISIONS][NTRIP];
  uint8_t bypass[NDIVISIONS][NTRIP];
  uint8_t trip[NDIVISIONS][NTRIP];
  uint8_t maintenance[NDIVISIONS];

  uint8_t actuators[2][NDEV];
};

struct test_state {
  uint32_t test;
  uint32_t test_timer;
  uint8_t self_test_running;
  uint8_t self_test_expect;

  uint8_t test_device_result[2];

  uint8_t test_instrumentation[2];
  uint8_t test_actuation_unit;
  uint8_t test_device;

  uint8_t test_instrumentation_done[4];
  uint8_t test_actuation_unit_done[2];
  uint8_t test_device_done[2];

  uint32_t test_setpoints[4][3];
  uint32_t test_inputs[4][2];
};

struct core_state {
  struct ui_values ui;
  struct test_state test;
};

int core_step(struct core_state *core);
#endif // CORE_H_
