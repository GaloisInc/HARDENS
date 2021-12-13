#ifndef INSTRUMENTATION_H_
#define INSTRUMENTATION_H_

#include "common.h"

#define T 0
#define P 1
#define S 2
#define NTRIP 3

#define BYPASS 0
#define OPERATE 1
#define TRIP 2

struct instrumentation_state {
  uint32_t reading[NTRIP];
  uint32_t setpoints[NTRIP];
  uint8_t sensor_trip[NTRIP];
  uint8_t mode[NTRIP];
  uint8_t maintenance;
};

void instrumentation_init(struct instrumentation_state *state);
int instrumentation_step(uint8_t div, struct instrumentation_state *state);

#endif // INSTRUMENTATION_H_
