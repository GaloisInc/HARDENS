#ifndef INSTRUMENTATION_H_
#define INSTRUMENTATION_H_

#include <stdint.h>

#define T 0
#define P 1
#define S 2
#define NTRIP 3

#define NCH 2

struct instrumentation_state {
  uint32_t reading[3];
  uint32_t setpoints[3];
  uint8_t bypass[NCH];
  uint8_t manual_trip[NTRIP];
  uint8_t sensor_trip[NTRIP];
  uint8_t maintenance;
};

struct set_bypass {
  uint8_t channel;
  uint8_t on;
};
struct set_maintenance {
  uint8_t on;
};
struct set_setpoint {
  uint8_t channel;
  uint32_t val;
};

#define SET_BYPASS 0
#define SET_MAINTENANCE 1
#define SET_SETPOINT 2

struct instrumentation_command {
  uint8_t type;
  union {
    struct set_bypass bypass;
    struct set_maintenance maintenance;
    struct set_setpoint setpoint;
  } cmd;
};

#endif // INSTRUMENTATION_H_
