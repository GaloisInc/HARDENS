#include "common.h"
#include "platform.h"
#include "instrumentation.h"
#include "actuation_logic.h"
#include "sense_actuate.h"

int instrumentation_step_generated_C(uint8_t div, struct instrumentation_state *state);
int instrumentation_step_handwritten_C(uint8_t div, struct instrumentation_state *state);
int instrumentation_step_generated_SystemVerilog(uint8_t div, struct instrumentation_state *state);
int instrumentation_step_handwritten_SystemVerilog(uint8_t div, struct instrumentation_state *state);
int actuation_unit_step_generated_C(uint8_t logic_no, struct actuation_logic *state);
int actuation_unit_step_generated_SystemVerilog(uint8_t logic_no, struct actuation_logic *state);


int sense_actuate_init(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation)
{
  instrumentation_init(&instrumentation[0]);
  instrumentation_init(&instrumentation[1]);
  actuation->vote_actuate[0] = 0;
  actuation->vote_actuate[1] = 0;

  return 0;
}

int sense_actuate_step_0(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation)
{
  int err = 0;
  err |= instrumentation_step_generated_C(0,&instrumentation[0]);
  err |= instrumentation_step_handwritten_C(1,&instrumentation[1]);
  // Do we think the devices should be actuated?
  err |= actuation_unit_step_generated_C(0,actuation);

  return err;
}

int sense_actuate_step_1(struct instrumentation_state *instrumentation,
                         struct actuation_logic *actuation)
{
  int err = 0;
  err |= instrumentation_step_handwritten_SystemVerilog(2,&instrumentation[0]);
  err |= instrumentation_step_generated_SystemVerilog(3,&instrumentation[1]);
  // Do we think the devices should be actuated?
  err |= actuation_unit_step_generated_SystemVerilog(1,actuation);

  return err;
}
