#ifndef COMMON_H_
#define COMMON_H_

#include <stdint.h>

// Instrumentation
#define NMODES 3
struct set_mode {
  uint8_t channel;
  uint8_t mode_val;
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

// Actuation
struct actuation_command {
    uint8_t device;
    uint8_t on;
};

// Core
#define INSTRUMENTATION_COMMAND 0
#define ACTUATION_COMMAND 1

struct rts_command {
  uint8_t type;
  uint8_t instrumentation_division;
  union {
    struct instrumentation_command instrumentation;
    struct actuation_command act;
  } cmd;
};

#endif // COMMON_H_
