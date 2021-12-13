#include "common.h"
#include "actuation_logic.h"
#include "platform.h"

#define w1 uint8_t
#define w2 uint8_t

// Return whether or not a device with the provided votes should be actuated
// Bit i = vote by logic unit i
extern w1 ActuateDevice(w2 vs4801);

int actuate_devices(void)
{
  int err = 0;
  for (int d = 0; d < NDEV; ++d) {
    uint8_t votes = 0;
    for (int l = 0; l < NVOTE_LOGIC; ++l) {
      uint8_t this_vote = 0;
      err |= get_actuation_state(l, d, &this_vote);
      votes |= (this_vote << d);
      // Call out to actuation policy
      err |= set_actuate_device(d, ActuateDevice(votes));
    }
  }

  return err;
}
