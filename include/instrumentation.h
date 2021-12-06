#ifndef INSTRUMENTATION_H_
#define INSTRUMENTATION_H_

#include <stdint.h>

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

struct set_mode {
  uint8_t channel;
  uint8_t mode;
};
struct set_maintenance {
  uint8_t on;
};
struct set_setpoint {
  uint8_t channel;
  uint32_t val;
};

#define SET_MODE 0
#define SET_MAINTENANCE 1
#define SET_SETPOINT 2

struct instrumentation_command {
  uint8_t type;
  union {
    struct set_mode mode;
    struct set_maintenance maintenance;
    struct set_setpoint setpoint;
  } cmd;
};

#endif // INSTRUMENTATION_H_
