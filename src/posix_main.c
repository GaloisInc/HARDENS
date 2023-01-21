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

#include "common.h"
#include "core.h"
#include "instrumentation.h"
#include "actuation_logic.h"
#include "sense_actuate.h"
#include "platform.h"

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
#include <time.h>

extern struct instrumentation_state instrumentation[4];
struct actuation_command *act_command_buf[2];

#define min(_a, _b) ((_a) < (_b) ? (_a) : (_b))
#define max(_a, _b) ((_a) > (_b) ? (_a) : (_b))

#include <pthread.h>
pthread_mutex_t display_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mem_mutex = PTHREAD_MUTEX_INITIALIZER;

#ifndef T0
#define T0 200
#endif

#ifndef P0
#define P0 1152600
#endif

// Bias to simulated sensor readings in degrees F
#ifndef T_BIAS
#define T_BIAS 0
#endif

// Bias to simulated sensor readings in 10^-5 lb/in2
#ifndef P_BIAS
#define P_BIAS 0
#endif

#ifndef SENSOR_UPDATE_MS
#define SENSOR_UPDATE_MS 500
#endif

int clear_screen() {
  return (isatty(fileno(stdin)) && (NULL == getenv("RTS_NOCLEAR")));
}

void update_display() {
  if (clear_screen()) {
    printf("\e[s\e[1;1H");//\e[2J");
  }
  for (int line = 0; line < NLINES; ++line) {
    printf("\e[0K");
    printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
  }
  if (clear_screen()) {
    printf("\e[u");
  }
}

int read_rts_command(struct rts_command *cmd) {
  int ok = 0;
  uint8_t device, on, div, ch, mode, sensor;
  uint32_t val;
  char *line = NULL;
  size_t linecap = 0;
  ssize_t linelen;

  /* if (isatty(fileno(stdin))) { */
  /*   set_display_line(&ui, 9, (char *)"> ", 0); */
  /* } */
  struct pollfd fds;
  fds.fd = STDIN_FILENO;
  fds.events = POLLIN;
  fds.revents = POLLIN;
  if(poll(&fds, 1, 100) < 1) {
    return 0;
  }
  linelen = getline(&line, &linecap, stdin);

  if (linelen == EOF)
    exit(0);

  if (linelen < 0)
    return 0;

  MUTEX_LOCK(&display_mutex);

  if (clear_screen()) {
    printf("\e[%d;1H\e[2K> ", NLINES+1);
  }

  MUTEX_UNLOCK(&display_mutex);

  if (2 == (ok = sscanf(line, "A %hhd %hhd", &device, &on))) {
    cmd->type = ACTUATION_COMMAND;
    cmd->cmd.act.device = device;
    cmd->cmd.act.on = on;
    DEBUG_PRINTF(("<main.c> read_rts_command ACTUATION_COMMAND dev=%u on=%u\n",
                  cmd->cmd.act.device, cmd->cmd.act.on));
    ok = 1;
  } else if (2 == (ok = sscanf(line, "M %hhd %hhd", &div, &on))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_MAINTENANCE;
    cmd->cmd.instrumentation.cmd.maintenance.on = on;
    DEBUG_PRINTF(("<main.c> read_rts_command INSTRUMENTATION_COMMAND MAINTENANCE div=%u on=%u, type=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.maintenance.on,
                  cmd->cmd.instrumentation.type));
    ASSERT(on == 0 || on == 1);
    ok = 1;
  } else if (3 == (ok = sscanf(line, "B %hhd %hhd %hhd", &div, &ch, &mode))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_MODE;
    cmd->cmd.instrumentation.cmd.mode.channel = ch;
    cmd->cmd.instrumentation.cmd.mode.mode_val = mode;
    DEBUG_PRINTF(("<main.c> read_rts_command INSTRUMENTATION_COMMAND MODE div=%u channel=%u mode=%u type=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.mode.channel,
                  cmd->cmd.instrumentation.cmd.mode.mode_val,
                  cmd->cmd.instrumentation.type));
    ok = 1;
  } else if (3 == (ok = sscanf(line, "S %hhd %hhd %d", &div, &ch, &val))) {
    cmd->type = INSTRUMENTATION_COMMAND;
    cmd->instrumentation_division = div;
    cmd->cmd.instrumentation.type = SET_SETPOINT;
    cmd->cmd.instrumentation.cmd.setpoint.channel = ch;
    cmd->cmd.instrumentation.cmd.setpoint.val = val;
    DEBUG_PRINTF(("<main.c> read_rts_command INSTRUMENTATION_COMMAND SETPOINT div=%u channel=%u val=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.setpoint.channel,
                  cmd->cmd.instrumentation.cmd.setpoint.val));
    ok = 1;
#ifndef SIMULATE_SENSORS
  } else if (3 == (ok = sscanf(line, "V %hhd %hhd %d", &sensor, &ch, &val))) {
    if (sensor < 2 && ch < 2)
      sensors[ch][sensor] = val;
    DEBUG_PRINTF(("<main.c> read_rts_command UPDATE SENSORS sensor=%d, ch=%d, val=%d\n",
          sensor,ch,val));
#endif
  } else if (line[0] == 'Q') {
    // printf("<main.c> read_rts_command QUIT\n");
    exit(0);
  } else if (line[0] == 'D') {
    DEBUG_PRINTF(("<main.c> read_rts_command UPDATE DISPLAY\n"));
    update_display();
  } else if (3 == (ok = sscanf(line, "ES %hhd %hhd %hhd", &sensor, &ch, &mode))) {
    error_sensor_mode[ch][sensor] = mode;
    DEBUG_PRINTF(("<main.c> read_rts_command ERROR SENSOR sensor=%d, ch=%d, mode=%d\n",
          sensor,ch,mode));
  } else if (2 == (ok = sscanf(line, "EI %hhd %hhd", &div, &mode))) {
    error_instrumentation_mode[div] = mode;
    DEBUG_PRINTF(("<main.c> read_rts_command ERROR INSTRUMENTATION div=%d, mode=%d\n",
          div,mode));
  }

  if (line)
    free(line);

  return ok;
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
  for (int c = 0; c < 2; ++c) {
    for (int s = 0; s < 2; ++s) {
      switch (error_sensor_mode[c][s]) {
        case 0:
          error_sensor[c][s] = 0;
          error_sensor_demux[c][s][0] = 0;
          error_sensor_demux[c][s][1] = 0;
          break;
        case 1:
          error_sensor[c][s] = 0;
          error_sensor_demux[c][s][0] = 1;
          error_sensor_demux[c][s][1] = 0;
          break;
        case 2:
          error_sensor[c][s] = 0;
          error_sensor_demux[c][s][0] = 0;
          error_sensor_demux[c][s][1] = 1;
          break;
        case 3:
          error_sensor[c][s] = 1;
          error_sensor_demux[c][s][0] = 0;
          error_sensor_demux[c][s][1] = 0;
          break;
        case 4:
        {
          int fail = rand() % 2;
          error_sensor[c][s] |= fail;
          error_sensor_demux[c][s][0] = 0;
          error_sensor_demux[c][s][1] = 0;
        }
        break;
        case 5:
        {
          error_sensor[c][s] = 0;
          error_sensor_demux[c][s][0] |= (rand() % 2);
          error_sensor_demux[c][s][1] |= (rand() % 2);
        }
        break;
        default:
          ASSERT("Invalid sensor fail mode" && 0);
      }
    }
  }
}

int update_sensor_simulation(void) {
  static int initialized = 0;
  static uint32_t last_update = 0;
  static uint32_t last[2][2] = {0};

  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  uint32_t t0 = last_update;
  uint32_t t = tp.tv_sec*1000 + tp.tv_nsec/1000000;

  if (!initialized) {
    last_update = t;
    last[0][T] = T0;
    last[1][T] = T0;
    last[0][P] = P0;
    last[1][P] = P0;
    initialized = 1;
  } else if (t - t0 > SENSOR_UPDATE_MS) {
    for (int s = 0; s < 2; ++s) {
      last[s][T] += (rand() % 7) - 3 + T_BIAS;
      // Don't stray too far from our steam table
      last[s][T] = min(last[s][T], 300);
      last[s][T] = max(last[s][T], 25);

      last[s][P] += (rand() % 7) - 3 + P_BIAS;
      // Don't stray too far from our steam table
      last[s][P] = min(last[s][P], 5775200);
      last[s][P] = max(last[s][P], 8000);
    }
    last_update = t;
  }
  sensors[T][0] = last[T][0];
  sensors[T][1] = last[T][1];
  sensors[P][0] = last[P][0];
  sensors[P][1] = last[P][1];

  return 0;
}

void update_sensors(void) {
  update_sensor_errors();
#ifdef SIMULATE_SENSORS
  update_sensor_simulation();
#endif
  for (int c = 0; c < 2; ++c) {
    for (int s = 0; s < 2; ++s) {
      if (error_sensor[c][s]) {
        sensors[c][s] = rand();
      }

      MUTEX_LOCK(&mem_mutex);
      sensors_demux[c][s][0] = sensors[c][s];
      MUTEX_UNLOCK(&mem_mutex);

      MUTEX_LOCK(&mem_mutex);
      sensors_demux[c][s][1] = sensors[c][s];
      MUTEX_UNLOCK(&mem_mutex);

      for (int d = 0; d < 2; ++d) {
        if(error_sensor_demux[c][s][d]) {
          MUTEX_LOCK(&mem_mutex);
          sensors_demux[c][s][d] = rand();
          MUTEX_UNLOCK(&mem_mutex);
        }
      }
    }
  }
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

int send_actuation_command(uint8_t id, struct actuation_command *cmd) {
  if (id < 2) {
    act_command_buf[id] = (struct actuation_command *)malloc(sizeof(*act_command_buf[id]));
    act_command_buf[id]->device = cmd->device;
    act_command_buf[id]->on = cmd->on;
    return 0;
  }
  return -1;
}

void* start0(void *arg) {
  while(1) {
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
  }
}
void* start1(void *arg) {
  while(1) {
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
  }
}

uint32_t time_in_s()
{
  static time_t start_time = 0;
  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  if (start_time == 0) {
    start_time = tp.tv_sec;
  }
  time_t total = tp.tv_sec - start_time;
  char line[256];
  sprintf(line, "Uptime: [%u]s\n",(uint32_t)total);
  set_display_line(&core.ui, 9, line, 0);
  return (uint32_t)total;
}

int main(int argc, char **argv) {
  struct rts_command *cmd = (struct rts_command *)malloc(sizeof(*cmd));

  core_init(&core);
  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);
  sense_actuate_init(1, &instrumentation[2], &actuation_logic[1]);

  if (isatty(fileno(stdin))) printf("\e[1;1H\e[2J");
  if (isatty(fileno(stdin))) printf("\e[%d;3H\e[2K> ", NLINES+1);

#ifdef USE_PTHREADS
  pthread_attr_t attr;
  pthread_t sense_actuate_0, sense_actuate_1;
  pthread_attr_init(&attr);
  pthread_create(&sense_actuate_0, &attr, start0, NULL);
  pthread_create(&sense_actuate_1, &attr, start1, NULL);
#endif

  while (1) {
    char line[256];
    fflush(stdout);
    MUTEX_LOCK(&display_mutex);
    sprintf(line, "HW ACTUATORS %s %s", actuator_state[0] ? "ON " : "OFF", actuator_state[1]? "ON " : "OFF");
    set_display_line(&core.ui, 8, line, 0);
    MUTEX_UNLOCK(&display_mutex);
    update_instrumentation_errors();
    update_sensors();
    core_step(&core);
#ifndef USE_PTHREADS
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
#endif
    update_display();
    sleep(1);
  }

  return 0;
}
