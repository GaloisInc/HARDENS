#ifndef ACTUATION_H_
#define ACTUATION_H_

#include "stdint.h"
#include "common.h"
#include "instrumentation.h"
#include "core.h"

#define CoincidenceL(trips)                                          \
((trips[0] != 0 && trips[1] != 0) ||                            \
     ((trips[0]  != 0|| trips[1] != 0) && (trips[2]  != 0|| trips[3] != 0)) || \
     (trips[2] != 0 && trips[3] != 0))

#define Coincidence(ch, trips) CoincidenceL(trips[ch])

/*@requires \valid(&trips[0.. NINSTR -1]);
  @assigns \nothing;
  @ensures (\result != 0) <==> CoincidenceL(trips);
*/
uint8_t Coincidence_2_4(uint8_t trips[4]);

/*@requires \valid(&trips[0.. NTRIP - 1][0.. NINSTR - 1]);
  @requires \valid(trips + (0.. NTRIP-1));
  @assigns \nothing;
  @ensures (\result != 0) <==> (old || Coincidence(0,trips) || Coincidence(1,trips));
*/
uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old);

/*@requires \valid(&trips[0.. NTRIP-1][0.. NINSTR-1]);
  @requires \valid(trips + (0.. NTRIP-1));
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
  @assigns state->manual_actuate[0.. NDEV-1];
  @assigns state->vote_actuate[0.. NDEV-1];
  @assigns core.test.actuation_old_vote;
  @assigns core.test.test_actuation_unit_done[logic_no];
*/
int actuation_unit_step(uint8_t logic_no, struct actuation_logic *state);

#endif // ACTUATION_H_
