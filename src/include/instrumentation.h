#ifndef INSTRUMENTATION_H_
#define INSTRUMENTATION_H_

#include "common.h"


uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3]);
uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t trip);

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
