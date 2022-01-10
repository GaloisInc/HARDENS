#include "common.h"
#include "actuate.h"
#include "actuation_logic.h"
#include "platform.h"

#define w1 uint8_t
#define w2 uint8_t

/*@ requires \true;
  @ assigns \nothing;
  @ ensures \true;
*/
int actuate_devices(void)
{
  int err = 0;
  /*@ loop invariant 0 <= d && d <= NDEV;
    @ loop assigns d, err;
    */
  for (int d = 0; d < NDEV; ++d) {
    uint8_t votes = 0;
    /*@ loop invariant 0 <= l && l <= NVOTE_LOGIC;
      @ loop assigns l, err, votes;
     */
    for (int l = 0; l < NVOTE_LOGIC; ++l) {
      uint8_t this_vote = 0;
      err |= get_actuation_state(l, d, &this_vote);
      votes |= (this_vote << d);
      // Call out to actuation policy
      err |= set_actuate_device(d, ActuateActuator(votes));
    }
  }

  return err;
}
