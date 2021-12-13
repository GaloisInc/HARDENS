#include "common.h"
#include "platform.h"
#include "instrumentation.h"
#include "actuation_logic.h"

int sense_actuate_init(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation)
{
  instrumentation_init(&instrumentation[0]);
  instrumentation_init(&instrumentation[1]);

  return 0;
}

int sense_actuate_step(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation)
{
  int err = 0;
  for (int i = 0; i < 2; ++i) {
    err |= instrumentation_step(core_id*2 + i, &instrumentation[i]);
  }
  // Do we think the devices should be actuated?
  err |= actuation_logic_step(core_id, actuation);

  return err;
}
