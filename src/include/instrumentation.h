#ifndef INSTRUMENTATION_H_
#define INSTRUMENTATION_H_

#include "platform.h"
#include "common.h"
#include "models.acsl"

#define ShouldTrip(_vals, _setpoints, _ch) \
  ((_ch == T && _vals[T] > _setpoints[T])     \
   ||  (_ch == P && _vals[P] > _setpoints[P])          \
   ||  (_ch == S && (int)_vals[S] < (int)_setpoints[S]))

/*@ assigns \nothing; */
uint32_t Saturation(uint32_t x, uint32_t y);

/*@requires \valid(vals + (0.. NTRIP-1));
  @requires \valid(setpoints + (0.. NTRIP-1));
  @assigns \nothing;
  @ensures \result == (uint8_t)Generate_Sensor_Trips(vals, setpoints);
*/
uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3]);

/*@requires \valid(vals + (0.. NTRIP-1));
  @requires \valid(setpoints + (0.. NTRIP-1));
  @requires ch < NTRIP;
  @assigns \nothing;
  @ensures \result == 0 || \result == 1;
  @ensures (\result == 1) <==> Trip(vals, setpoints, ch);
*/
uint8_t Trip(uint32_t vals[3], uint32_t setpoints[3], uint8_t ch);

/*@requires mode < NMODES;
  @requires trip <= 1;
  @assigns \nothing;
  @ensures (\result != 0) <==> Is_Ch_Tripped(mode, trip != 0);
*/
uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t trip);

struct instrumentation_state {
  uint32_t reading[NTRIP];
  uint32_t test_reading[NTRIP];
  uint32_t setpoints[NTRIP];
  uint8_t sensor_trip[NTRIP];
  uint8_t mode[NTRIP];
  uint8_t maintenance;
  uint8_t test_complete;
};

void instrumentation_init(struct instrumentation_state *state);

/*@requires \valid(state);
  @requires \valid(state->reading + (0.. NTRIP-1));
  @requires \valid(state->test_reading + (0.. NTRIP-1));
  @requires \valid(state->setpoints + (0.. NTRIP-1));
  @requires \valid(state->sensor_trip + (0.. NTRIP-1));
  @requires state->mode[T] \in {BYPASS, OPERATE, TRIP};
  @requires state->mode[P] \in {BYPASS, OPERATE, TRIP};
  @requires state->mode[S] \in {BYPASS, OPERATE, TRIP};
  @requires div < NTRIP;
  @assigns state->reading[0.. NTRIP-1];
  @assigns state->test_reading[0.. NTRIP-1];
  @assigns state->setpoints[0.. NTRIP-1];
  @assigns state->sensor_trip[0.. NTRIP-1];
  @assigns state->maintenance;
  @assigns state->mode[0.. NTRIP-1];
  @assigns core.test.test_instrumentation_done[div];
  @ensures state->mode[T] \in {BYPASS, OPERATE, TRIP};
  @ensures state->mode[P] \in {BYPASS, OPERATE, TRIP};
  @ensures state->mode[S] \in {BYPASS, OPERATE, TRIP};
*/
int instrumentation_step(uint8_t div, struct instrumentation_state *state);

int instrumentation_step_generated_C(uint8_t div, struct instrumentation_state *state);
int instrumentation_step_handwritten_C(uint8_t div, struct instrumentation_state *state);
int instrumentation_step_generated_SystemVerilog(uint8_t div, struct instrumentation_state *state);
int instrumentation_step_handwritten_SystemVerilog(uint8_t div, struct instrumentation_state *state);
#endif // INSTRUMENTATION_H_
