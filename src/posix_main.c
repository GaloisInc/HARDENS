#include "actuation_logic.h"
#include "core.h"
#include "sense_actuate.h"
#include "instrumentation.h"
#include "platform.h"
#include <assert.h>
#include <poll.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/_pthread/_pthread_mutex_t.h>
#include <termios.h>
#include <unistd.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/select.h>
#include <time.h>

#define min(_a, _b) ((_a) < (_b) ? (_a) : (_b))
#define max(_a, _b) ((_a) > (_b) ? (_a) : (_b))

#ifdef USE_PTHREADS
#include <pthread.h>
pthread_mutex_t display_mutex = PTHREAD_MUTEX_INITIALIZER;
pthread_mutex_t mem_mutex = PTHREAD_MUTEX_INITIALIZER;
#else
#define pthread_mutex_lock(x)
#define pthread_mutex_unlock(x)
#endif

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

struct core_state core = {0};
struct instrumentation_state instrumentation[4];
struct actuation_logic actuation_logic[2];

uint32_t sensors[4][2];
uint8_t trip_signals[NTRIP][4];
struct instrumentation_command *inst_command_buf[4];

uint8_t actuator_state[NDEV];
uint8_t device_actuation_logic[2][NDEV];
struct actuation_command *act_command_buf[2];

uint8_t error_instrumentation[NINSTR];
// Simulate sensor failure and demux failure, i.e.:
// error_sensor[T][0] simulates temperature demux 1 failure, while
// error_sensor[T][0] && error_sensor[T][1] simulates temperature 1 failure
uint8_t error_sensor[2][NINSTR];

void update_display() {
  if (isatty(fileno(stdin))) {
    printf("\e[s\e[1;1H");//\e[2J");
  }
  for (int line = 0; line < NLINES; ++line) {
    printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
  }
  /* if (isatty(fileno(stdin))) printf("\e[%d;1H\e[2K>\e[u",NLINES+1); */
  if (isatty(fileno(stdin))) printf("\e[u");
}


int read_instrumentation_trip_signals(uint8_t arr[3][4]) {
  for (int i = 0; i < NTRIP; ++i) {
    for (int div = 0; div < 4; ++div) {
      pthread_mutex_lock(&mem_mutex);
      arr[i][div] = trip_signals[i][div];
      pthread_mutex_unlock(&mem_mutex);
    }
  }

  return 0;
}

int set_actuate_device(uint8_t device_no, uint8_t on)
{
  pthread_mutex_lock(&mem_mutex);
  actuator_state[device_no] = on;
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}

int read_rts_command(struct rts_command *cmd) {
  int ok = 0;
  uint8_t device, on, div, ch, mode;
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

  pthread_mutex_lock(&display_mutex);
  if (isatty(fileno(stdin)))
      printf("\e[%d;1H\e[2K> ", NLINES+1);
  pthread_mutex_unlock(&display_mutex);

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
  } else if (line[0] == 'D') {
    update_display();
  } else if (3 == (ok = sscanf(line, "ES %hhd %hhd %hhd", &ch, &div, &mode))) {
    error_sensor[ch][div] = mode;
    // Error Sensor
  }

  if (line)
    free(line);

  return ok;
}

#ifndef SIMULATE_SENSORS
int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  pthread_mutex_lock(&mem_mutex);
  if (!error_sensor[channel][div]) {
    *val = sensors[div][channel];
  }
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}
#else
int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  pthread_mutex_lock(&mem_mutex);
  static int initialized[4][2] = {0};
  static uint32_t last[4][2] = {0};
  static uint32_t last_update[4][2] = {0};

  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);
  uint32_t t0 = last_update[div][channel];
  uint32_t t = tp.tv_sec*1000 + tp.tv_nsec/1000000;

  if (!initialized[div][channel]) {
    last_update[div][channel] = t;
    initialized[div][channel] = 1;
    // Saturation values taken from pressure table
    if (channel == T) {
      last[div][channel] = T0;
    } else {
      last[div][channel] = P0;
    }
  } else if (t - t0 > SENSOR_UPDATE_MS) {
    if (channel == T) {
      last[div][channel] += (rand() % 7) - 3 + T_BIAS;
      // Don't stray too far from our steam table
      last[div][channel] = min(last[div][channel], 300);
      last[div][channel] = max(last[div][channel], 25);
    } else {
      last[div][channel] += (rand() % 7) - 3 + P_BIAS;
      // Don't stray too far from our steam table
      last[div][channel] = min(last[div][channel], 5775200);
      last[div][channel] = max(last[div][channel], 8000);
    }
    last_update[div][channel] = t;
  }
  pthread_mutex_unlock(&mem_mutex);

  *val = last[div][channel];
  return 0;
}

#endif

int set_output_instrumentation_trip(uint8_t div, uint8_t channel, uint8_t val) {
  pthread_mutex_lock(&mem_mutex);
  if (!error_instrumentation[div])
    trip_signals[channel][div] = val;
  pthread_mutex_unlock(&mem_mutex);
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
  pthread_mutex_lock(&mem_mutex);
  actuation_logic[logic_no].vote_actuate[device_no] = reset_val;
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}

int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on) {
  assert(logic_no < 2);
  assert(device_no < 2);

  /* assert(!(logic_no == 1 && on)); */

  pthread_mutex_lock(&mem_mutex);
  device_actuation_logic[logic_no][device_no] = on;
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value) {
  pthread_mutex_lock(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].reading[ch];
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}

int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value) {
  pthread_mutex_lock(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].sensor_trip[ch];
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}

int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value) {
  pthread_mutex_lock(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].mode[ch];
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}

int get_instrumentation_maintenance(uint8_t division, uint8_t *value) {
  pthread_mutex_lock(&mem_mutex);
  if (!error_instrumentation[division])
    *value = instrumentation[division].maintenance;
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}

int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value) {
  pthread_mutex_lock(&mem_mutex);
  *value = device_actuation_logic[i][device];
  pthread_mutex_unlock(&mem_mutex);
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
  pthread_mutex_lock(&mem_mutex);
  core.test.test_instrumentation_done[div] = v;
  pthread_mutex_unlock(&mem_mutex);
}

int is_instrumentation_test_complete(uint8_t id)
{
  pthread_mutex_lock(&mem_mutex);
  int ret = core.test.test_instrumentation_done[id];
  pthread_mutex_unlock(&mem_mutex);
  return ret;
}

uint8_t get_test_actuation_unit()
{
  pthread_mutex_lock(&mem_mutex);
  uint8_t ret = core.test.test_actuation_unit;
  pthread_mutex_unlock(&mem_mutex);
  return ret;
}

void set_actuation_unit_test_complete(uint8_t div, int v)
{
  pthread_mutex_lock(&mem_mutex);
  core.test.test_actuation_unit_done[div] = v;
  pthread_mutex_unlock(&mem_mutex);
}

void set_actuation_unit_test_input_vote(uint8_t id, int v)
{
  pthread_mutex_lock(&mem_mutex);
  core.test.actuation_old_vote = v != 0;
  pthread_mutex_unlock(&mem_mutex);
}

int is_actuation_unit_test_complete(uint8_t id)
{
  pthread_mutex_lock(&mem_mutex);
  int ret = core.test.test_actuation_unit_done[id];
  pthread_mutex_unlock(&mem_mutex);
  return ret;
}

void set_actuate_test_result(uint8_t dev, uint8_t result)
{
  pthread_mutex_lock(&mem_mutex);
  core.test.test_device_result[dev] = result;
  pthread_mutex_unlock(&mem_mutex);
}

void set_actuate_test_complete(uint8_t dev, int v)
{
  pthread_mutex_lock(&mem_mutex);
  core.test.test_device_done[dev] = v;
  pthread_mutex_unlock(&mem_mutex);
}

int is_actuate_test_complete(uint8_t dev)
{
  pthread_mutex_lock(&mem_mutex);
  int ret = core.test.test_device_done[dev];
  pthread_mutex_unlock(&mem_mutex);
  return ret;
}

int read_test_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val)
{
  pthread_mutex_lock(&mem_mutex);
  *val = core.test.test_inputs[div][channel];
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}

uint8_t is_test_running()
{
  pthread_mutex_lock(&mem_mutex);
  uint8_t ret = core.test.self_test_running;
  pthread_mutex_unlock(&mem_mutex);
  return ret;
}

void set_test_running(int val)
{
  pthread_mutex_lock(&mem_mutex);
  core.test.self_test_running = val;
  pthread_mutex_unlock(&mem_mutex);
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
  struct timespec tp;
  clock_gettime(CLOCK_REALTIME, &tp);

  time_t total = tp.tv_sec;

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
    pthread_mutex_lock(&display_mutex);
    sprintf(line, "HW ACTUATORS %s %s", actuator_state[0] ? "ON " : "OFF", actuator_state[1]? "ON " : "OFF");
    set_display_line(&core.ui, 8, line, 0);
    pthread_mutex_unlock(&display_mutex);
    core_step(&core);
#ifndef USE_PTHREADS
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
#endif
    if (isatty(fileno(stdin))) {
      update_display();
    }
  }

  return 0;
}
