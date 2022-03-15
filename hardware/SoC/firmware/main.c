/**
 * Main program entry for RTS
 */
// System includes
#include <stdint.h>

// Board includes
#include "bsp.h"
#include "printf.h"

// RTS includes
#include "actuation_logic.h"
#include "core.h"
#include "sense_actuate.h"
#include "instrumentation.h"
#include "platform.h"

// There is no better min/max in C?
#define min(_a, _b) ((_a) < (_b) ? (_a) : (_b))
#define max(_a, _b) ((_a) > (_b) ? (_a) : (_b))

struct core_state core = {0};
struct instrumentation_state instrumentation[4];
struct actuation_logic actuation_logic[2];

// channel -> sensor # -> val
uint32_t sensors[2][2];
// channel -> sensor # -> demux output # -> val
uint32_t sensors_demux[2][2][2];

uint8_t trip_signals[NTRIP][4];
struct instrumentation_command *inst_command_buf[4];

uint8_t actuator_state[NDEV];
uint8_t device_actuation_logic[2][NDEV];
struct actuation_command *act_command_buf[2];

// EI mode:
//   mode = 0 => no error
//   mode = 1 => error
//   mode = 2 => nondet error
uint8_t error_instrumentation_mode[NINSTR];
uint8_t error_instrumentation[NINSTR];
// ES ch mode:
//   mode = 0 => no error
//   mode = 1 => demux error (out 0)
//   mode = 2 => demux error (out 1)
//   mode = 3 => sensor error (error in both demux outs)
//   mode = 4 => nondet sensor error
//   mode = 5 => nondet demux error
uint8_t error_sensor_mode[2][2];
uint8_t error_sensor[2][2];
uint8_t error_sensor_demux[2][2][2];

void update_display()
{
  // TODO
}

int read_instrumentation_trip_signals(uint8_t arr[3][4])
{
  for (int i = 0; i < NTRIP; ++i)
  {
    for (int div = 0; div < 4; ++div)
    {
      arr[i][div] = trip_signals[i][div];
    }
  }

  return 0;
}

int set_actuate_device(uint8_t device_no, uint8_t on)
{
  actuator_state[device_no] = on;
  return 0;
}

int read_rts_command(struct rts_command *cmd)
{
  // TODO
  return 0;
}


void update_instrumentation_errors(void) {
  for (int i = 0; i < NINSTR; ++i) {
    if(error_instrumentation_mode[i] == 2) {
      error_instrumentation[i] |= rand() % 2;
    } else {
      error_instrumentation[i] = error_instrumentation_mode[i];
    }
  }
}

void update_sensor_errors(void) {
  // TODO
}

int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  int sensor = div/2;
  int demux_out = div%2;
  *val = sensors_demux[channel][sensor][demux_out];
  return 0;
}

// NOTE: This will be different for SoC impl run
void update_sensors(void) {
  // TODO
}

int set_output_instrumentation_trip(uint8_t div, uint8_t channel, uint8_t val) {
  if (!error_instrumentation[div])
    trip_signals[channel][div] = val;
  return 0;
}

// NOTE: This will be different for SoC impl run - maybe a GPIO write?
int send_actuation_command(uint8_t id, struct actuation_command *cmd) {
  if (id < 2) {
    act_command_buf[id] = (struct actuation_command *)malloc(sizeof(*act_command_buf[id]));
    act_command_buf[id]->device = cmd->device;
    act_command_buf[id]->on = cmd->on;
    return 0;
  }
  return -1;
}

int read_actuation_command(uint8_t id, struct actuation_command *cmd) {
  struct actuation_command *c = act_command_buf[id];
  if (c) {
    cmd->device = c->device;
    cmd->on = c->on;
    free(c);
    act_command_buf[id] = NULL;
    return 1;
  }
  return 0;
}

int read_instrumentation_command(uint8_t div,
                                 struct instrumentation_command *cmd) {
  struct instrumentation_command *c = inst_command_buf[div];
  if (c) {
    cmd->type = c->type;
    cmd->cmd = c->cmd;
    free(c);
    inst_command_buf[div] = NULL;
    return 1;
  }
  return 0;
}

int send_instrumentation_command(uint8_t id,
                                 struct instrumentation_command *cmd) {
  if (id < 4) {
    inst_command_buf[id] = (struct instrumentation_command *)malloc(sizeof(*inst_command_buf[id]));
    inst_command_buf[id]->type = cmd->type;
    inst_command_buf[id]->cmd = cmd->cmd;
    return 0;
  }
  return -1;
}

int reset_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t reset_val) {
  actuation_logic[logic_no].vote_actuate[device_no] = reset_val;
  return 0;
}

int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on) {
  device_actuation_logic[logic_no][device_no] = on;
  return 0;
}

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value) {
  if (!error_instrumentation[division])
    *value = instrumentation[division].reading[ch];
  return 0;
}

int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value) {
  if (!error_instrumentation[division])
    *value = instrumentation[division].sensor_trip[ch];
  return 0;
}

int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value) {
  if (!error_instrumentation[division])
    *value = instrumentation[division].mode[ch];
  return 0;
}

int get_instrumentation_maintenance(uint8_t division, uint8_t *value) {
  if (!error_instrumentation[division])
    *value = instrumentation[division].maintenance;
  return 0;
}

int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value) {
  *value = device_actuation_logic[i][device];
  return 0;
}

uint8_t get_test_device()
{
  return core.test.test_device;
}

void get_test_instrumentation(uint8_t *id)
{
  id[0] = core.test.test_instrumentation[0];
  id[1] = core.test.test_instrumentation[1];
}

int get_instrumentation_test_setpoints(uint8_t id, uint32_t *setpoints)
{
  setpoints[0] = core.test.test_setpoints[id][0];
  setpoints[1] = core.test.test_setpoints[id][1];
  setpoints[2] = core.test.test_setpoints[id][2];
  return 0;
}

void set_instrumentation_test_complete(uint8_t div, int v)
{
  core.test.test_instrumentation_done[div] = v;
}

int is_instrumentation_test_complete(uint8_t id)
{
  int ret = core.test.test_instrumentation_done[id];
  return ret;
}

uint8_t get_test_actuation_unit()
{
  uint8_t ret = core.test.test_actuation_unit;
  return ret;
}

void set_actuation_unit_test_complete(uint8_t div, int v)
{
  core.test.test_actuation_unit_done[div] = v;
}

void set_actuation_unit_test_input_vote(uint8_t id, int v)
{
  core.test.actuation_old_vote = v != 0;
}

int is_actuation_unit_test_complete(uint8_t id)
{
  int ret = core.test.test_actuation_unit_done[id];
  return ret;
}

void set_actuate_test_result(uint8_t dev, uint8_t result)
{
  core.test.test_device_result[dev] = result;
}

void set_actuate_test_complete(uint8_t dev, int v)
{
  core.test.test_device_done[dev] = v;
}

int is_actuate_test_complete(uint8_t dev)
{
  int ret = core.test.test_device_done[dev];
  return ret;
}

int read_test_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val)
{
  *val = core.test.test_inputs[div][channel];
  return 0;
}

uint8_t is_test_running()
{
  uint8_t ret = core.test.self_test_running;
  return ret;
}

void set_test_running(int val)
{
  core.test.self_test_running = val;
}



int instrumentation_step_generated_C(uint8_t div, struct instrumentation_state *state)
{
  return 0;
}

int instrumentation_step_handwritten_C(uint8_t div, struct instrumentation_state *state)
{
  return 0;
}

int instrumentation_step_generated_SystemVerilog(uint8_t div, struct instrumentation_state *state)
{
  return 0;
}

int instrumentation_step_handwritten_SystemVerilog(uint8_t div, struct instrumentation_state *state)
{
  return 0;
}

int actuation_unit_step_generated_C(uint8_t logic_no, struct actuation_logic *state)
{
  return 0;
}

int actuation_unit_step_generated_SystemVerilog(uint8_t logic_no, struct actuation_logic *state)
{
  return 0;
}

int actuate_devices_generated_C(void)
{
  //TODO
}



int main(void)
{
  printf("Hello world\n");
  struct rts_command *cmd = (struct rts_command *)malloc(sizeof(*cmd));
  core_init(&core);
  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);
  sense_actuate_init(1, &instrumentation[2], &actuation_logic[1]);

  while (1)
  {
    printf("%u miliseconds passed\n",time_in_ms());
    // TODO: update sensors
    // update_sensors();
    core_step(&core);
    delay_ms(1000);
  }

  return 0;
}
