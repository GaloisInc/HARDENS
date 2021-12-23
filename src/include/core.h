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

int core_step(struct ui_values *ui);
#endif // CORE_H_
