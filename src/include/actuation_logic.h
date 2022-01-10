#ifndef ACTUATION_H_
#define ACTUATION_H_

#include "stdint.h"
#include "common.h"
#include "instrumentation.h"

#define CoincidenceL(trips)                                          \
((trips[0] != 0 && trips[1] != 0) ||                            \
     ((trips[0]  != 0|| trips[1] != 0) && (trips[2]  != 0|| trips[3] != 0)) || \
     (trips[2] != 0 && trips[3] != 0))

#define Coincidence(ch, trips) CoincidenceL(trips[ch])

/*@requires \valid(trips + (0..3));
  @assigns \nothing;
  @ensures (\result != 0) <==> CoincidenceL(trips);
*/
uint8_t Coincidence_2_4(uint8_t trips[4]);

/*@requires \valid(trips + (0..2));
  @requires \valid(trips[0..2] + (0..3));
  @assigns \nothing;
  @ensures (\result != 0) <==> (old || Coincidence(0,trips) || Coincidence(1,trips));
*/
uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old);

/*@requires \valid(trips + (0..2));
  @requires \valid(trips[0..2] + (0..3));
  @assigns \nothing;
  @ensures (Coincidence(2,trips)) ==> (\result != 0);
*/
uint8_t Actuate_D1(uint8_t trips[3][4], uint8_t old);

struct actuation_logic {
    uint8_t vote_actuate[NDEV];
    uint8_t manual_actuate[NDEV];
};

/* The main logic of the actuation unit */
/*@requires \valid(state);
  @requires logic_no <= 1;
  @assigns state->manual_actuate[0..1];
  @assigns state->vote_actuate[0..1];
*/
int actuation_unit_step(uint8_t logic_no, struct actuation_logic *state);

#endif // ACTUATION_H_
