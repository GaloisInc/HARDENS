#include "instrumentation.h"

void instrumentation_init(struct instrumentation_state *state) {
  state->maintenance = 1;
  for (int i = 0; i < NTRIP; ++i) {
    state->mode[i] = 0;
    state->reading[i] = 0;
    state->sensor_trip[i] = 0;
    state->setpoints[i] = 0;
  }
}
