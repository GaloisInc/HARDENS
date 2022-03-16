#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include "platform.h"
#include "common.h"
#include "core.h"
#include "instrumentation.h"
#include "actuation_logic.h"
#include "sense_actuate.h"


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

//EI mode:
//  mode = 0 => no error
//  mode = 1 => error
//  mode = 2 => nondet error
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

int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  MUTEX_LOCK(&mem_mutex);
  int sensor = div/2;
  int demux_out = div%2;
  *val = sensors_demux[channel][sensor][demux_out];
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].reading[ch];
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].sensor_trip[ch];
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].mode[ch];
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

int get_instrumentation_maintenance(uint8_t division, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].maintenance;
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  *value = device_actuation_logic[i][device];
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

int read_instrumentation_trip_signals(uint8_t arr[3][4]) {
  for (int i = 0; i < NTRIP; ++i) {
    for (int div = 0; div < 4; ++div) {
      MUTEX_LOCK(&mem_mutex);
      arr[i][div] = trip_signals[i][div];
      MUTEX_UNLOCK(&mem_mutex);
    }
  }
  return 0;
}

int reset_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t reset_val) {
  MUTEX_LOCK(&mem_mutex);
  actuation_logic[logic_no].vote_actuate[device_no] = reset_val;
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on) {
  ASSERT(logic_no < 2);
  ASSERT(device_no < 2);

  MUTEX_LOCK(&mem_mutex);
  device_actuation_logic[logic_no][device_no] = on;
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

int set_output_instrumentation_trip(uint8_t div, uint8_t channel, uint8_t val) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[div])
    trip_signals[channel][div] = val;
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

int set_actuate_device(uint8_t device_no, uint8_t on)
{
  MUTEX_LOCK(&mem_mutex);
  actuator_state[device_no] = on;
  MUTEX_UNLOCK(&mem_mutex);
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

uint8_t is_test_running()
{
  MUTEX_LOCK(&mem_mutex);
  uint8_t ret = core.test.self_test_running;
  MUTEX_UNLOCK(&mem_mutex);
  return ret;
}

void set_test_running(int val)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.self_test_running = val;
  MUTEX_UNLOCK(&mem_mutex);
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
  MUTEX_LOCK(&mem_mutex);
  core.test.test_instrumentation_done[div] = v;
  MUTEX_UNLOCK(&mem_mutex);
}

int is_instrumentation_test_complete(uint8_t id)
{
  MUTEX_LOCK(&mem_mutex);
  int ret = core.test.test_instrumentation_done[id];
  MUTEX_UNLOCK(&mem_mutex);
  return ret;
}

int read_test_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val)
{
  MUTEX_LOCK(&mem_mutex);
  *val = core.test.test_inputs[div][channel];
  MUTEX_UNLOCK(&mem_mutex);
  return 0;
}

uint8_t get_test_actuation_unit()
{
  MUTEX_LOCK(&mem_mutex);
  uint8_t ret = core.test.test_actuation_unit;
  MUTEX_UNLOCK(&mem_mutex);
  return ret;
}

void set_actuation_unit_test_complete(uint8_t div, int v)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.test_actuation_unit_done[div] = v;
  MUTEX_UNLOCK(&mem_mutex);
}

void set_actuation_unit_test_input_vote(uint8_t id, int v)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.actuation_old_vote = v != 0;
  MUTEX_UNLOCK(&mem_mutex);
}

int is_actuation_unit_test_complete(uint8_t id)
{
  MUTEX_LOCK(&mem_mutex);
  int ret = core.test.test_actuation_unit_done[id];
  MUTEX_UNLOCK(&mem_mutex);
  return ret;
}

void set_actuate_test_result(uint8_t dev, uint8_t result)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.test_device_result[dev] = result;
  MUTEX_UNLOCK(&mem_mutex);
}

void set_actuate_test_complete(uint8_t dev, int v)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.test_device_done[dev] = v;
  MUTEX_UNLOCK(&mem_mutex);
}

int is_actuate_test_complete(uint8_t dev)
{
  MUTEX_LOCK(&mem_mutex);
  int ret = core.test.test_device_done[dev];
  MUTEX_UNLOCK(&mem_mutex);
  return ret;
}