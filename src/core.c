#include "core.h"
#include "platform.h"
#include "actuate.h"
#include "rts.h"
#include <string.h>

#ifdef PLATFORM_HOST
#include <stdio.h>
#else
#include "printf.h"
#endif

#define INST_OFFSET 0
#define ACT_OFFSET 5
char INSTR_LINE_FMT[] = "#I %d (%c): T[%10d %c %d] P[%10d %c %d] S[%10d %c %d]";
char ACT_LINE_FMT[] = "#A %d [%d %d]";

const char self_test_running[]     = "SELF TEST:     RUNNING";
const char self_test_not_running[] = "SELF TEST: NOT RUNNING";
const char pass[] = "LAST TEST: PASS";
const char fail[] = "LAST TEST: FAIL";

char sensor_warning[] = "WARNING: LARGE SENSOR DIFFERENTIAL";
char sensor_ok[] = "SENSORS OK";

struct testcase {
  uint32_t input[4][2];
  uint32_t setpoints[4][3];
  uint8_t instrumentation[2];
  uint8_t actuation_unit;
  uint8_t device;
  uint8_t expect;
} tests[] = {
// Test data generated from Cryptol RTS::SelfTestOracleHalf
#include "self_test_data/tests.inc.c"
};

char mode_char(uint8_t mode) {
  switch (mode) {
  case BYPASS:
    return 'B';
  case OPERATE:
    return 'O';
  case TRIP:
    return 'T';
  default:
    return '?';
  }
}

char maint_char(uint8_t mode) {
  if (mode)
    return 'M';
  else
    return '_';
}

int update_ui_instr(struct ui_values *ui) {
  int err = 0;
  int sensor_differential = 0;

  char line[256];

  for (uint8_t i = 0; i < NDIVISIONS; ++i) {
    for (uint8_t ch = 0; ch < NTRIP; ++ch) {
      if ((err = get_instrumentation_value(i, ch, &ui->values[i][ch])) < 0)
        return err;
      if ((err = get_instrumentation_mode(i, ch, &ui->bypass[i][ch])) < 0)
        return err;
      if ((err = get_instrumentation_trip(i, ch, &ui->trip[i][ch])) < 0)
        return err;
    }
    if ((err = get_instrumentation_maintenance(i, &ui->maintenance[i])) < 0)
      return err;

    snprintf(line, sizeof(line), INSTR_LINE_FMT, INST_OFFSET + i,
             maint_char(ui->maintenance[i]), ui->values[i][T],
             mode_char(ui->bypass[i][T]), 0 != ui->trip[i][T], ui->values[i][P],
             mode_char(ui->bypass[i][P]), 0 != ui->trip[i][P], ui->values[i][S],
             mode_char(ui->bypass[i][S]), 0 != ui->trip[i][S]);

    set_display_line(ui, i, line, sizeof(line));
  }

  // Flag any sensor differences that exceed thresholds
  for (uint8_t i = 0; i < NDIVISIONS; ++i) {

    if (ui->maintenance[i])
      continue;

    for (uint8_t j = 0; j < NDIVISIONS; ++j) {

      if (ui->maintenance[j])
        continue;

      sensor_differential |=
        (ui->values[i][T] > ui->values[j][T] &&
         ui->values[i][T] - ui->values[j][T] > T_THRESHOLD);
      sensor_differential |=
        (ui->values[i][P] > ui->values[j][P] &&
         ui->values[i][P] - ui->values[j][P] > P_THRESHOLD);
    }
  }

  if (sensor_differential)
    set_display_line(ui, 14, sensor_warning, sizeof(sensor_warning));
  else
    set_display_line(ui, 14, sensor_ok, sizeof(sensor_ok));

  return err;
}

int update_ui_actuation(struct ui_values *ui) {
  int err = 0;
  for (int i = 0; i < 2; ++i) {
    char line[256];
    for (int d = 0; d < 2; ++d) {
      uint8_t val;
      err |= get_actuation_state(i, d, &val);
      ui->actuators[i][d] = val;
    }
    snprintf(line, sizeof(line), ACT_LINE_FMT, i, ui->actuators[i][0],
             ui->actuators[i][1]);
    set_display_line(ui, ACT_OFFSET + i, line, sizeof(line));
  }

  return err;
}

int update_ui(struct ui_values *ui) {
  int err = 0;
  err |= update_ui_instr(ui);
  err |= update_ui_actuation(ui);

  return err;
}

int set_display_line(struct ui_values *ui, uint8_t line_number, char *display, uint32_t size) {
  memset(ui->display[line_number], ' ', LINELENGTH);
  strncpy(ui->display[line_number], (const char*)display, LINELENGTH);
  return 0;
}

int end_test(struct test_state *test, struct ui_values *ui) {
    int passed =
         test->test_device_result[test->test_device]
      == (test->self_test_expect || test->actuation_old_vote);
    test->failed = !passed;

    // Reset state
    set_test_running(0);

    if (passed) {
      set_display_line(ui, 16, (char*)pass, 0);
      test->test++;
      if (test->test >= sizeof(tests)/sizeof(struct testcase)) {
        test->test = 0;
        test->test_timer_start = time_in_s();
      }
    } else {
      set_display_line(ui, 16, (char*)fail, 0);
      set_display_line(ui, 20, (char*)"A TEST FAILED", 0);
    }

    return passed;
}

int components_ready() {
  return !is_instrumentation_test_complete(0)
         && !is_instrumentation_test_complete(1)
         && !is_instrumentation_test_complete(2)
         && !is_instrumentation_test_complete(3)
         && !is_actuation_unit_test_complete(0)
         && !is_actuation_unit_test_complete(1)
         && !is_actuate_test_complete(0)
         && !is_actuate_test_complete(1);
}

int self_test_timer_expired(struct test_state *test) {
  uint32_t t    = time_in_s();
  uint32_t diff = t - test->test_timer_start;

  return SELF_TEST_PERIOD_SEC < diff;
}

int should_start_self_test(struct test_state *test) {
  return (!is_test_running()) && (self_test_timer_expired(test) || (test->test != 0));
}

int test_step(struct test_state *test, struct ui_values *ui) {
  int err = 0;

  if(!test->failed && should_start_self_test(test)) {
    if (components_ready())
    {
      struct testcase *next = &tests[test->test];
      test->self_test_expect = next->expect;
      test->test_device = next->device;
      test->test_actuation_unit = next->actuation_unit;
      memcpy(test->test_instrumentation, next->instrumentation, 2);
      memcpy(test->test_inputs, next->input, 2*4*sizeof(uint32_t));
      memcpy(test->test_setpoints, next->setpoints, 3*4*sizeof(uint32_t));

      set_test_running(1);
      set_display_line(ui, 15, (char *)self_test_running, 0);
    }
  } else if (is_test_running() && test->test_device_done[test->test_device]) {
    int passed = end_test(test, ui);
    if(!passed) err = -1;
  } else if (!is_test_running()) {
    set_display_line(ui, 15, (char *)self_test_not_running, 0);
  }

  return err;
}

void core_init(struct core_state *c) {
  c->test.test_timer_start = time_in_s();
  c->test.failed = 0;
}

int core_step(struct core_state *c) {
  int err = 0;
  struct rts_command rts;

  if (!c->error) {
    // Actuate devices if necessary
    actuate_devices_generated_C();
  }

  // Let's allow command processing even if an error is detected.
  // In a real system, we would probably want to disconnect the device
  // and perform maintenance.
  int read_cmd = read_rts_command(&rts);
  if (read_cmd < 0) {
    err |= -read_cmd;
  } else if (read_cmd > 0) {
    switch (rts.type) {
    case INSTRUMENTATION_COMMAND:
      err |= send_instrumentation_command(rts.instrumentation_division,
                                          &rts.cmd.instrumentation);
      break;

    case ACTUATION_COMMAND:
      err |= send_actuation_command(0, &rts.cmd.act);
      err |= send_actuation_command(1, &rts.cmd.act);
      break;

    default:
      break;
    }
  }

  err |= test_step(&c->test, &c->ui);
  err |= update_ui(&c->ui);

  c->error = err;
  return err;
}
