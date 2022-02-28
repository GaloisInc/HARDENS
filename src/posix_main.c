#include "actuation_logic.h"
#include "core.h"
#include "sense_actuate.h"
#include "instrumentation.h"
#include "platform.h"
#include <assert.h>
#include <poll.h>
#include <fcntl.h>
#include <stdio.h>
#include <pthread.h>
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
  if (clear_screen()) printf("\e[u");
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

  pthread_mutex_lock(&display_mutex);

  if (clear_screen())
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
    assert(on == 0 || on == 1);
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
  } else if (3 == (ok = sscanf(line, "V %hhd %hhd %d", &sensor, &ch, &val))) {
    if (sensor < 2 && ch < 2)
      sensors[ch][sensor] = val;
#endif
  } else if (line[0] == 'Q') {
    exit(0);
  } else if (line[0] == 'D') {
    update_display();
  } else if (3 == (ok = sscanf(line, "ES %hhd %hhd %hhd", &sensor, &ch, &mode))) {
    error_sensor_mode[ch][sensor] = mode;
  } else if (2 == (ok = sscanf(line, "EI %hhd %hhd", &div, &mode))) {
    error_instrumentation_mode[div] = mode;
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
          assert("Invalid sensor fail mode" && 0);
      }
    }
  }
}

int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val) {
  pthread_mutex_lock(&mem_mutex);
  int sensor = div/2;
  int demux_out = div%2;
  *val = sensors_demux[channel][sensor][demux_out];
  pthread_mutex_unlock(&mem_mutex);
  return 0;
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
  }
  sensors[0][T] = last[0][T];
  sensors[1][T] = last[1][T];
  sensors[0][P] = last[0][P];
  sensors[1][P] = last[1][P];

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

      pthread_mutex_lock(&mem_mutex);
      sensors_demux[c][s][0] = sensors[c][s];
      pthread_mutex_unlock(&mem_mutex);

      pthread_mutex_lock(&mem_mutex);
      sensors_demux[c][s][1] = sensors[c][s];
      pthread_mutex_unlock(&mem_mutex);

      for (int d = 0; d < 2; ++d) {
        if(error_sensor_demux[c][s][d]) {
          pthread_mutex_lock(&mem_mutex);
          sensors_demux[c][s][d] = rand();
          pthread_mutex_unlock(&mem_mutex);
        }
      }
    }
  }
}

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
  pthread_mutex_lock(&mem_mutex);
  actuation_logic[logic_no].vote_actuate[device_no] = reset_val;
  pthread_mutex_unlock(&mem_mutex);
  return 0;
}

int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on) {
  assert(logic_no < 2);
  assert(device_no < 2);

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
    update_instrumentation_errors();
    update_sensors();
    core_step(&core);
#ifndef USE_PTHREADS
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
#endif
    update_display();
  }

  return 0;
}
