// HARDENS Reactor Trip System (RTS)

// Copyright 2021, 2022, 2023 Galois, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include "platform.h"
#include "common.h"
#include "core.h"
#include "instrumentation.h"
#include "actuation_logic.h"
#include "sense_actuate.h"

#ifdef PLATFORM_HOST
#include <stdio.h>
#else
#include "printf.h"
#endif

struct core_state core = {0};
struct instrumentation_state instrumentation[4];
struct actuation_logic actuation_logic[2];

// channel -> sensor # -> val
uint32_t sensors[2][2];
// channel -> sensor # -> demux output # -> val
uint32_t sensors_demux[2][2][2];

uint8_t trip_signals[NTRIP][4];
struct instrumentation_command inst_command_buf[4];

uint8_t actuator_state[NDEV];
uint8_t device_actuation_logic[2][NDEV];

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
  DEBUG_PRINTF(("<common.c> read_instrumentation_channel: div=%u,channel=%u,val=%u\n",div,channel,*val));
  return 0;
}

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].reading[ch];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_instrumentation_value: error=%u, division=%u,ch=%u,val=%u\n",error_instrumentation[division], division,ch,*value));
  return 0;
}

int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].sensor_trip[ch];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_instrumentation_trip: error=%u, division=%u,ch=%u,val=%u\n",error_instrumentation[division], division,ch,*value));
  return 0;
}

int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].mode[ch];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_instrumentation_mode: error=%u, division=%u,ch=%u,val=%u\n",error_instrumentation[division], division,ch,*value));
  return 0;
}

int get_instrumentation_maintenance(uint8_t division, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].maintenance;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_instrumentation_maintenance: error=%u, division=%u,val=%u\n",error_instrumentation[division],division,*value));
  return 0;
}

int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value) {
  MUTEX_LOCK(&mem_mutex);
  *value = device_actuation_logic[i][device];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_actuation_state: i=%u,device=%u,val=%u\n",i,device,*value));
  return 0;
}

int read_instrumentation_trip_signals(uint8_t arr[3][4]) {
  DEBUG_PRINTF(("<common.c> read_instrumentation_trip_signals: ["));
  for (int i = 0; i < NTRIP; ++i) {
    DEBUG_PRINTF(("["));
    for (int div = 0; div < 4; ++div) {
      MUTEX_LOCK(&mem_mutex);
      arr[i][div] = trip_signals[i][div];
      DEBUG_PRINTF(("%u",trip_signals[i][div]));
      MUTEX_UNLOCK(&mem_mutex);
    }
    DEBUG_PRINTF(("],"));
  }
  DEBUG_PRINTF(("]\n"));
  return 0;
}

int reset_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t reset_val) {
  MUTEX_LOCK(&mem_mutex);
  actuation_logic[logic_no].vote_actuate[device_no] = reset_val;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> reset_actuation_logic: logic_no=%u,device=%u,reset_val=%u\n",logic_no,device_no,reset_val));
  return 0;
}

int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on) {
  ASSERT(logic_no < 2);
  ASSERT(device_no < 2);

  MUTEX_LOCK(&mem_mutex);
  device_actuation_logic[logic_no][device_no] = on;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_output_actuation_logic: logic_no=%u,device=%u,on=%u\n",logic_no,device_no,on));
  return 0;
}

int set_output_instrumentation_trip(uint8_t div, uint8_t channel, uint8_t val) {
  MUTEX_LOCK(&mem_mutex);
  if (!error_instrumentation[div])
    trip_signals[channel][div] = val;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_output_instrumentation_trip: error=%u,div=%u,channel=%u,val=%u\n",error_instrumentation[div], div, channel, val));
  return 0;
}

int set_actuate_device(uint8_t device_no, uint8_t on)
{
  MUTEX_LOCK(&mem_mutex);
  actuator_state[device_no] = on;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_actuate_device: dev %u, on %u\n",device_no, on));
  return 0;
}

int read_instrumentation_command(uint8_t div,
                                 struct instrumentation_command *cmd) {
  DEBUG_PRINTF(("<common.c> read_instrumentation_command\n"));
  if ((div < 4) && (inst_command_buf[div].valid == 1)) {
    cmd->type = inst_command_buf[div].type;
    cmd->cmd = inst_command_buf[div].cmd;
    inst_command_buf[div].valid = 0;
    return 1;
  }
  return 0;
}

int send_instrumentation_command(uint8_t div,
                                 struct instrumentation_command *cmd) {
  DEBUG_PRINTF(("<common.c> send_instrumentation_command\n"));
  if (div < 4) {
    inst_command_buf[div].type = cmd->type;
    inst_command_buf[div].cmd = cmd->cmd;
    inst_command_buf[div].valid = 1;
    return 0;
  }
  return -1;
}

uint8_t is_test_running()
{
  MUTEX_LOCK(&mem_mutex);
  uint8_t ret = core.test.self_test_running;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> is_test_running? %u\n",ret));
  return ret;
}

void set_test_running(int val)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.self_test_running = val;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_test_running: %i\n",core.test.self_test_running));
}

uint8_t get_test_device()
{
  DEBUG_PRINTF(("<common.c> get_test_device: %u\n",core.test.test_device));
  return core.test.test_device;
}

void get_test_instrumentation(uint8_t *id)
{
  id[0] = core.test.test_instrumentation[0];
  id[1] = core.test.test_instrumentation[1];
  DEBUG_PRINTF(("<common.c> get_test_instrumentation\n"));
}

int get_instrumentation_test_setpoints(uint8_t id, uint32_t *setpoints)
{
  setpoints[0] = core.test.test_setpoints[id][0];
  setpoints[1] = core.test.test_setpoints[id][1];
  setpoints[2] = core.test.test_setpoints[id][2];
  DEBUG_PRINTF(("<common.c> get_instrumentation_test_setpoints\n"));
  return 0;
}

void set_instrumentation_test_complete(uint8_t div, int v)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.test_instrumentation_done[div] = v;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_instrumentation_test_complete: div=%u,v=%i\n",div,v));
}

int is_instrumentation_test_complete(uint8_t id)
{
  MUTEX_LOCK(&mem_mutex);
  int ret = core.test.test_instrumentation_done[id];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> is_instrumentation_test_complete: id=%u,ret=%i\n",id,ret));
  return ret;
}

int read_test_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val)
{
  MUTEX_LOCK(&mem_mutex);
  *val = core.test.test_inputs[div][channel];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> read_test_instrumentation_channel: div=%u,channel=%u,val=%u\n",div,channel,*val));
  return 0;
}

uint8_t get_test_actuation_unit()
{
  MUTEX_LOCK(&mem_mutex);
  uint8_t ret = core.test.test_actuation_unit;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> get_test_actuation_unit: %u\n",ret));
  return ret;
}

void set_actuation_unit_test_complete(uint8_t div, int v)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.test_actuation_unit_done[div] = v;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_actuation_unit_test_complete: div %u, v=%i\n",div,v));
}

void set_actuation_unit_test_input_vote(uint8_t id, int v)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.actuation_old_vote = v != 0;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_actuation_unit_test_input_vote: id %u, v=%i\n",id,v));
}

int is_actuation_unit_test_complete(uint8_t id)
{
  MUTEX_LOCK(&mem_mutex);
  int ret = core.test.test_actuation_unit_done[id];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> is_actuation_unit_test_complete: %i\n",ret));
  return ret;
}

void set_actuate_test_result(uint8_t dev, uint8_t result)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.test_device_result[dev] = result;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_actuate_test_result: dev %u, result=%u\n",dev,result));
}

void set_actuate_test_complete(uint8_t dev, int v)
{
  MUTEX_LOCK(&mem_mutex);
  core.test.test_device_done[dev] = v;
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> set_actuate_test_complete: dev %u, v=%i\n",dev,v));
}

int is_actuate_test_complete(uint8_t dev)
{
  MUTEX_LOCK(&mem_mutex);
  int ret = core.test.test_device_done[dev];
  MUTEX_UNLOCK(&mem_mutex);
  DEBUG_PRINTF(("<common.c> is_actuate_test_complete: %i\n",ret));
  return ret;
}
