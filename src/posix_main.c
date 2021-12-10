#include "actuation.h"
#include "core.h"
#include "instrumentation.h"
#include "platform.h"
#include <assert.h>

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

struct instrumentation_state instrumentation[4];
struct actuation_logic actuation_logic[2];

static uint32_t sensors[4][2];
static uint8_t trip_signals[4][NTRIP];
struct instrumentation_command *inst_command_buf[4];

static uint8_t device_actuation[2][NDEV];
struct actuation_command *act_command_buf[2];

int read_trip_signals(uint8_t arr[4][3]) {
  for (int div = 0; div < 4; ++div) {
    for (int i = 0; i < NTRIP; ++i) {
      arr[div][i] = trip_signals[div][i];
    }
  }

  return 0;
}

int read_rts_command(struct rts_command *cmd) {
  int ok = 0;
  uint8_t device, on, div, ch, mode;
  uint32_t val;
  char *line = NULL;
  size_t linecap = 0;
  ssize_t linelen;

  linelen = getline(&line, &linecap, stdin);
  if (linelen < 0)
    return 0;

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
  } else if (3 == (ok = sscanf(line, "V %hhd %hhd %d", &div, &ch, &val))) {
    if (div < 4 && ch < 3)
      sensors[div][ch] = val;
  } else if (line[0] == 'Q') {
    exit(0);
  }

  if (line)
    free(line);

  return ok;
}

int read_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  *val = sensors[div][channel];
  return 0;
}

int set_output_trip(uint8_t div, uint8_t channel, uint8_t val) {
  trip_signals[div][channel] = val;
  return 0;
}

int send_actuation_command(uint8_t id, struct actuation_command *cmd) {
  if (id < 2) {
    act_command_buf[id] = malloc(sizeof(*act_command_buf[id]));
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
    inst_command_buf[id] = malloc(sizeof(*inst_command_buf[id]));
    inst_command_buf[id]->type = cmd->type;
    inst_command_buf[id]->cmd = cmd->cmd;
    return 1;
  }
  return 0;
}

int actuate_device(uint8_t logic_no, uint8_t device_no, uint8_t on) {
  assert(logic_no < 2);
  assert(device_no < 2);
  device_actuation[logic_no][device_no] = on;
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
  *value = device_actuation[i][device];
  return 0;
}

int set_display_line(uint8_t line_number, char *display, uint32_t size) {
  return printf("\e[%d;0H%s\n", line_number + 1, display);
}

int main(int argc, char **argv) {
  struct ui_values ui;
  struct rts_command *cmd = malloc(sizeof(*cmd));

  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);
  sense_actuate_init(1, &instrumentation[2], &actuation_logic[1]);

  printf("\e[1;1H\e[2J");
  while (1) {
    printf("\e[8;1H\e[2K");
    core_step(&ui);
    sense_actuate_step(0, &instrumentation[0], &actuation_logic[0]);
    sense_actuate_step(1, &instrumentation[2], &actuation_logic[1]);
  }

  return 0;
}
