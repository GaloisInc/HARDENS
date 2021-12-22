#include "instrumentation.h"
#include "platform.h"
#include "common.h"

#define TRIP_I(_v, _i) (((_v) >> (_i)) & 0x1)

static int saturation(uint32_t x, uint32_t y)
{
    return y == 0 ? 0 : (x / y);
}

static int instrumentation_step_trip(uint8_t div,
                                     struct instrumentation_state *state) {
  int err = 0;
  err |= read_instrumentation_channel(div, T, &state->reading[T]);
  err |= read_instrumentation_channel(div, P, &state->reading[P]);
  state->reading[S] = saturation(state->reading[T], state->reading[P]);

  uint8_t new_trips = Generate_Sensor_Trips(state->reading, state->setpoints);
  for (int i = 0; i < NTRIP; ++i) {
    state->sensor_trip[i] = TRIP_I(new_trips, i);
  }

  return err;
}

static int instrumentation_handle_command(uint8_t div,
                                          struct instrumentation_command *i_cmd,
                                          struct instrumentation_state *state) {
  struct set_maintenance set_maint;
  struct set_mode set_mode;
  struct set_setpoint set_setpoint;

  switch (i_cmd->type) {
  case SET_MAINTENANCE:
    set_maint = i_cmd->cmd.maintenance;
    state->maintenance = set_maint.on;
    break;

  case SET_MODE:
    set_mode = i_cmd->cmd.mode;
    if (state->maintenance && set_mode.channel < NTRIP &&
        set_mode.mode_val < NMODES) {
      state->mode[set_mode.channel] = set_mode.mode_val;
    }
    break;

  case SET_SETPOINT:
    set_setpoint = i_cmd->cmd.setpoint;
    if (state->maintenance && set_setpoint.channel < NTRIP) {
      state->setpoints[set_setpoint.channel] = set_setpoint.val;
    }
    break;

  default:
    return -1;
  }

  return 0;
}

static int instrumentation_set_output_trips(uint8_t div,
                                            struct instrumentation_state *state) {
  for (int i = 0; i < NTRIP; ++i) {
    set_output_instrumentation_trip(div, i,
                    Is_Ch_Tripped(state->mode[i], state->sensor_trip[i]));
  }
  return 0;
}

int instrumentation_step(uint8_t div, struct instrumentation_state *state) {
  int err = 0;
  /* Read trip signals & vote */
  err |= instrumentation_step_trip(div, state);

  /* Handle any external commands */
  struct instrumentation_command i_cmd;
  int read_cmd = read_instrumentation_command(div, &i_cmd);
  if (read_cmd > 0) {
    err |= instrumentation_handle_command(div, &i_cmd, state);
  } else if (read_cmd < 0) {
    err |= -read_cmd;
  }

  /* Actuate devices based on voting and commands */
  err |= instrumentation_set_output_trips(div, state);
  return err;
}
