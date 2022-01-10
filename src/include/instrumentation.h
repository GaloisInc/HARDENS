#ifndef INSTRUMENTATION_H_
#define INSTRUMENTATION_H_

#include "common.h"

#define ShouldTrip(_vals, _setpoints, _ch) \
  ((_ch == 0 && _vals[0] > _setpoints[0])     \
   ||  (_ch == 1 && _vals[1] > _setpoints[1])          \
   ||  (_ch == 2 && (int)_vals[2] < (int)_setpoints[2]))

uint32_t Saturation(uint32_t x, uint32_t y);

/*@requires \valid(vals + (0..2));
  @requires \valid(setpoints + (0..2));
  @assigns \nothing;
  @ensures ((\result & 0x1) != 0) <==> ShouldTrip(vals, setpoints, 0);
  @ensures ((\result & 0x2) != 0) <==> ShouldTrip(vals, setpoints, 1);
  @ensures ((\result & 0x4) != 0) <==> ShouldTrip(vals, setpoints, 2);
*/
uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3]);

/*@requires \valid(vals + (0..2));
  @requires \valid(setpoints + (0..2));
  @requires ch <= 2;
  @assigns \nothing;
  @ensures \result == 0 || \result == 1;
  @ensures (\result == 1) ==> ShouldTrip(vals, setpoints, ch);
  @ensures (\result == 0) ==> !ShouldTrip(vals, setpoints, ch);
*/
uint8_t Trip(uint32_t vals[3], uint32_t setpoints[3], uint8_t ch);

/*@requires mode <= 2;
  @assigns \nothing;
behavior manual_trip:
  @requires (mode == 2);
  @ensures  (\result != 0);
behavior bypass_trip:
  @requires (mode == 0);
  @ensures (\result == 0);
behavior normal:
  @requires (trip == 0 || trip == 1);
  @ensures (\result == 0) <==> (trip == 0);
*/
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
