#ifndef INSTRUMENTATION_H_
#define INSTRUMENTATION_H_

#include "platform.h"
#include "common.h"

#define ShouldTrip(_vals, _setpoints, _ch) \
  ((_ch == 0 && _vals[0] > _setpoints[0])     \
   ||  (_ch == 1 && _vals[1] > _setpoints[1])          \
   ||  (_ch == 2 && (int)_vals[2] < (int)_setpoints[2]))

/*@ assigns \nothing; */
uint32_t Saturation(uint32_t x, uint32_t y);

/*@requires \valid(vals + (0.. NTRIP-1));
  @requires \valid(setpoints + (0.. NTRIP-1));
  @assigns \nothing;
  @ensures ((\result & 0x1) != 0) <==> ShouldTrip(vals, setpoints, 0);
  @ensures ((\result & 0x2) != 0) <==> ShouldTrip(vals, setpoints, 1);
  @ensures ((\result & 0x4) != 0) <==> ShouldTrip(vals, setpoints, 2);
*/
uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3]);

/*@requires \valid(vals + (0.. NTRIP-1));
  @requires \valid(setpoints + (0.. NTRIP-1));
  @requires ch < NTRIP;
  @assigns \nothing;
  @ensures \result == 0 || \result == 1;
  @ensures (\result == 1) ==> ShouldTrip(vals, setpoints, ch);
  @ensures (\result == 0) ==> !ShouldTrip(vals, setpoints, ch);
*/
uint8_t Trip(uint32_t vals[3], uint32_t setpoints[3], uint8_t ch);

/*@requires mode < NMODES;
  @requires trip <= 1;
  @assigns \nothing;
  @ensures (\result != 0) <==> ((mode == 2) || (mode == 1 && trip != 0));
*/
uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t trip);

struct instrumentation_state {
  uint32_t reading[NTRIP];
  uint32_t setpoints[NTRIP];
  uint8_t sensor_trip[NTRIP];
  uint8_t mode[NTRIP];
  uint8_t maintenance;
  uint8_t test_complete;
};

void instrumentation_init(struct instrumentation_state *state);

/*@requires \valid(state);
  @requires \valid(state->reading + (0.. NTRIP-1));
  @requires \valid(state->setpoints + (0.. NTRIP-1));
  @requires \valid(state->sensor_trip + (0.. NTRIP-1));
  @requires state->mode[0] \in {0,1,2};
  @requires state->mode[1] \in {0,1,2};
  @requires state->mode[2] \in {0,1,2};
  @requires div < NTRIP;
  @assigns state->reading[0.. NTRIP-1];
  @assigns state->setpoints[0.. NTRIP-1];
  @assigns state->sensor_trip[0.. NTRIP-1];
  @assigns state->maintenance;
  @assigns state->mode[0.. NMODES-1];
  @assigns core.test.test_instrumentation_done[div];
  @ensures state->mode[0] \in {0,1,2};
  @ensures state->mode[1] \in {0,1,2};
  @ensures state->mode[2] \in {0,1,2};
*/
int instrumentation_step(uint8_t div, struct instrumentation_state *state);
#endif // INSTRUMENTATION_H_
