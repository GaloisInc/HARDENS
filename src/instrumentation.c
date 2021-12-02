#include "instrumentation.h"

#define TRIP_I(_v, _i) (((_v) >> (_i)) & 0x1)

uint8_t Generate_Sensor_Trips(uint8_t bypass[2], uint32_t vals[3], uint32_t setpoints[3]);

/* Read the value of channel `channel`, setting *val on success;
 * @return < 0 on error
 */
extern int read_channel(uint8_t channel, uint32_t *val);

extern uint32_t saturation(uint32_t temp, uint32_t pressure);

extern int
read_instrumentation_command(struct instrumentation_command *cmd);

extern int
set_output_trip(uint8_t channel, uint8_t val);

int
instrumentation_step_trip(struct instrumentation_state *state)
{
  int err = 0;
  /* get state */
  uint32_t reading[NTRIP];
  /* calculate setpoint */
  if ((err = read_channel(T, &reading[T])) < 0) return err;
  if ((err = read_channel(P, &reading[P])) < 0) return err;
  /* update trip signals */
  uint8_t new_trips = Generate_Sensor_Trips(state->bypass, reading, state->setpoints);
  for (int i = 0; i < NTRIP; ++i) {
    state->sensor_trip[i] |= TRIP_I(new_trips, i);
  }

  return 0;
}

int
instrumentation_handle_command(struct instrumentation_state *state)
{
  int ok = 0;
  struct instrumentation_command cmd;

  if ((ok = read_instrumentation_command(&cmd)) < 0) return ok;

  if (ok > 0) {
    switch (cmd.type) {
      case SET_MAINTENANCE:
        state->maintenance = cmd.cmd.maintenance.on;
        break;

      case SET_BYPASS:
        if (state->maintenance && cmd.cmd.bypass.channel < NCH) {
          state->bypass[cmd.cmd.bypass.channel] = cmd.cmd.bypass.on;
        }
        break;

      case SET_SETPOINT:
        if (state->maintenance && cmd.cmd.setpoint.channel < NCH) {
          state->setpoints[cmd.cmd.setpoint.channel] = cmd.cmd.setpoint.val;
        }
        break;

      default:
        return -1;
    }
  }

  return 0;
}

int
instrumentation_set_output_trips(struct instrumentation_state *state)
{
  for (int i = 0; i < NTRIP; ++i) {
    set_output_trip(i, state->manual_trip[i] || state->sensor_trip[i]);
  }
  return 0;
}

int
instrumentation_step(struct instrumentation_state *state)
{
    int err = 0;
    /* Read trip signals & vote */
    err = instrumentation_step_trip(state);
    if(err < 0) return err;

    /* Handle any external commands */
    err = instrumentation_handle_command(state);
    if(err < 0) return err;

    /* Actuate devices based on voting and commands */
    err = instrumentation_set_output_trips(state);
    return err;
}
