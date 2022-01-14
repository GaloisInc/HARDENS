#include "common.h"
#include "actuate.h"
#include "actuation_logic.h"
#include "platform.h"
#include <assert.h>

#define w1 uint8_t
#define w2 uint8_t

// Return whether or not a device with the provided votes should be actuated
// Bit i = vote by logic unit i
extern w1 ActuateActuator(w2 vs4801);

int actuate_devices(void)
{
  int err = 0;
  int do_test = is_test_running() && is_actuation_unit_test_complete(get_test_actuation_unit());
  if (do_test && is_actuate_test_complete(get_test_device()))
    return 0;
  if (!do_test) {
    set_actuate_test_complete(0, 0);
    set_actuate_test_complete(1, 0);
  }

  for (int d = 0; d < NDEV; ++d) {
    uint8_t votes = 0;
    uint8_t test_votes = 0;
    for (int l = 0; l < NVOTE_LOGIC; ++l) {
      uint8_t this_vote = 0;
      uint8_t valid = get_actuation_unit_output_valid(l);
      err   |= get_actuation_state(l, d, &this_vote);
      if (!do_test && valid)
        assert(this_vote == 0);
      if (do_test && l == 0 && d == 0) {
        assert(this_vote != 0);
      }
      if (do_test && l == get_test_actuation_unit())
        test_votes |= (this_vote << d);
      else if(valid)
        votes |= (this_vote << d);
    }

    if (do_test && d == get_test_device()) {
      if (!is_actuate_test_complete(get_test_device())) {
        assert(ActuateActuator(test_votes));
        set_actuate_test_result(d, ActuateActuator(test_votes));
        set_actuate_test_complete(d, 1);
      }
    }

    // Call out to actuation policy
    err |= set_actuate_device(d, ActuateActuator(votes));
  }

  return err;
}
