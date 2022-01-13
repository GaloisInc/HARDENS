#include "actuation_logic.h"
#include "core.h"
#include "sense_actuate.h"
#include "instrumentation.h"
#include "platform.h"
#include <assert.h>
#include <poll.h>
#include <fcntl.h>
#include <stdio.h>
#include <termios.h>
#include <unistd.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
struct core_state core = {0};

struct instrumentation_state instrumentation[4];
struct actuation_logic actuation_logic[2];

static uint32_t sensors[4][2];
static uint8_t trip_signals[NTRIP][4];
struct instrumentation_command *inst_command_buf[4];

static uint8_t actuator_state[NDEV];
static uint8_t device_actuation_logic[2][NDEV];
struct actuation_command *act_command_buf[2];

int read_instrumentation_trip_signals(uint8_t arr[3][4]) {
  for (int i = 0; i < NTRIP; ++i) {
    for (int div = 0; div < 4; ++div) {
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

int read_rts_command(struct rts_command *cmd) {
  int ok = 0;
  uint8_t device, on, div, ch, mode;
  uint32_t val;
  char *line = NULL;
  size_t linecap = 0;
  ssize_t linelen;

  if (isatty(fileno(stdin))) {
    set_display_line(9, (char *)"> ", 0);
  }
  struct pollfd fds;
  fds.fd = STDIN_FILENO;
  fds.events = POLLIN;
  fds.revents = POLLIN;
  if(poll(&fds, 1, 500) < 1) {
    return 0;
  }
  linelen = getline(&line, &linecap, stdin);

  if (linelen == EOF)
    exit(0);

  if (linelen < 0)
    return 0;

  if (isatty(fileno(stdin)))
      printf("\e[10;3H\e[2K");
  if (2 == (ok = sscanf(line, "A %hhd %hhd", &device, &on))) {
    cmd->type = ACTUATION_COMMAND;
    cmd->cmd.act.device = device;
    cmd->cmd.act.on = on;
    ok = 1;
  } else if (2 == (ok = sscanf(line, "M %hhd %hhd", &div, &on))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_MAINTENANCE;
    cmd->cmd.instrumentation.cmd.maintenance.on = on;
    ok = 1;
  } else if (3 == (ok = sscanf(line, "B %hhd %hhd %hhd", &div, &ch, &mode))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_MODE;
    cmd->cmd.instrumentation.cmd.mode.channel = ch;
    cmd->cmd.instrumentation.cmd.mode.mode_val = mode;
    ok = 1;
  } else if (3 == (ok = sscanf(line, "S %hhd %hhd %d", &div, &ch, &val))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_SETPOINT;
    cmd->cmd.instrumentation.cmd.setpoint.channel = ch;
    cmd->cmd.instrumentation.cmd.setpoint.val = val;
    ok = 1;
#ifndef SIMULATE_SENSORS
  } else if (3 == (ok = sscanf(line, "V %hhd %hhd %d", &div, &ch, &val))) {
    if (div < 4 && ch < 3)
      sensors[div][ch] = val;
#endif
  } else if (line[0] == 'Q') {
    exit(0);
  }

  if (line)
    free(line);

  return ok;
}

#ifndef SIMULATE_SENSORS
int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  *val = sensors[div][channel];
  return 0;
}
#else
int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  static int initialized[2] = {0};
  static int last = 0;
  if (!initialized[channel]) {
    initialized[channel] = 1;
    if (channel == 0) {
      last = rand() % 300;
    } else {
      last = rand() % 60;
    }
  } else {
    if (channel == 0) {
      last += (rand() % 7) - 3;
    } else {
      last += (rand() % 3) - 1;
    }
  }

  *val = last;
  return 0;
}

#endif

int set_output_instrumentation_trip(uint8_t div, uint8_t channel, uint8_t val) {
  trip_signals[channel][div] = val;
  return 0;
}

int send_actuation_command(uint8_t id, struct actuation_command *cmd) {
  if (id < 2) {
    act_command_buf[id] = (struct actuation_command *)malloc(sizeof(*act_command_buf[id]));
    act_command_buf[id]->device = cmd->device;
    act_command_buf[id]->on = cmd->on;
  }
  return 0;
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
    return 1;
  }
  return 0;
}

int reset_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t reset_val) {
  actuation_logic[logic_no].vote_actuate[device_no] = reset_val;
  return 0;
}

int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on) {
  assert(logic_no < 2);
  assert(device_no < 2);
  device_actuation_logic[logic_no][device_no] = on;
  return 0;
}

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value) {
  *value = instrumentation[division].reading[ch];
  return 0;
}

int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value) {
  *value = instrumentation[division].sensor_trip[ch];
  return 0;
}

int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value) {
  *value = instrumentation[division].mode[ch];
  return 0;
}

int get_instrumentation_maintenance(uint8_t division, uint8_t *value) {
  *value = instrumentation[division].maintenance;
  return 0;
}

int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value) {
  *value = device_actuation_logic[i][device];
  return 0;
}

int set_display_line(uint8_t line_number, const char *display, uint32_t size) {
  if (isatty(fileno(stdin))) {
    return printf("\e[s\e[%d;1H%s\e[u", line_number + 1, display);
  }
  else
    return printf("%s\n", display);
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

void set_instrumentation_test_complete(uint8_t div)
{
  core.test.test_instrumentation_done[div] = 1;
}

int is_instrumentation_test_complete(uint8_t id)
{
  return core.test.test_instrumentation_done[id];
}

uint8_t get_test_actuation_unit()
{
  return core.test.test_actuation_unit;
}

void set_actuation_unit_test_complete(uint8_t div)
{
  core.test.test_actuation_unit_done[div] = 1;
}

int is_actuation_unit_test_complete(uint8_t id)
{
  return core.test.test_actuation_unit_done[id];
}

void set_actuate_test_result(uint8_t dev, uint8_t result)
{
  core.test.test_device_result[dev] = result;
}

void set_actuate_test_complete(uint8_t dev)
{
  core.test.test_device_done[dev] = 1;
}

int is_actuate_test_complete(uint8_t dev)
{
  return core.test.test_device_done[dev];
}

int read_test_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val)
{
  *val = core.test.test_inputs[div][channel];
  return 0;
}

uint8_t is_test_running() {
  return core.test.self_test_running;
}

int main(int argc, char **argv) {
  struct rts_command *cmd = (struct rts_command *)malloc(sizeof(*cmd));

  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);
  sense_actuate_init(1, &instrumentation[2], &actuation_logic[1]);


  core.test.test_timer = 0x00000002;
  core.test.test_instrumentation[0] = 0;
  core.test.test_instrumentation[1] = 1;
  core.test.test_actuation_unit = 0;
  core.test.test_device = 0;
  core.test.self_test_expect = 1;
  memcpy(core.test.test_inputs, (uint32_t[4][2]){{30,0}, {30,0}, {0,0}, {0,0}}, 8*sizeof(uint32_t));;
  memcpy(core.test.test_setpoints, (uint32_t[4][3]){{10,10,10}, {10,10,10}, {10,10,10}, {10,10,10}}, 12*sizeof(uint32_t));;

  if (isatty(fileno(stdin))) printf("\e[1;1H\e[2J");
  if (isatty(fileno(stdin))) printf("\e[10;3H\e[2K");
  while (1) {
    char line[256];
    fflush(stdout);
    sprintf(line, "HW ACTUATORS %s %s", actuator_state[0] ? "ON " : "OFF", actuator_state[1]? "ON " : "OFF");
    set_display_line(8, line, 0);
    core_step(&core);
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
  }

  return 0;
}
