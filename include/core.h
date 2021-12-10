#ifndef CORE_H_
#define CORE_H_

#include "common.h"
#include "instrumentation.h"
#include "actuation.h"

#define NDIVISIONS 4

struct ui_values {
  uint32_t values[NDIVISIONS][NTRIP];
  uint8_t bypass[NDIVISIONS][NTRIP];
  uint8_t trip[NDIVISIONS][NTRIP];
  uint8_t maintenance[NDIVISIONS];

  uint8_t actuators[2][NDEV];
};

int core_step(struct ui_values *ui);

int sense_actuate_init(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation);

int sense_actuate_step(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation);
#endif // CORE_H_
