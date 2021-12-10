#include "common.h"
#include "platform.h"
#include "instrumentation.h"
#include "actuation.h"

int sense_actuate_init(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation)
{
  instrumentation_init(&instrumentation[0]);
  instrumentation_init(&instrumentation[1]);
}

int sense_actuate_step(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation)
{
  for (int i = 0; i < 2; ++i) {
    instrumentation_step(core_id*2 + i, &instrumentation[i]);
  }
  actuation_step(core_id, actuation);

  return 0;
}
