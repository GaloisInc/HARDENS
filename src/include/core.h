#ifndef CORE_H_
#define CORE_H_

#include "common.h"

#ifndef SELF_TEST_PERIOD_SEC
#define SELF_TEST_PERIOD_SEC 20
#endif

#define NDIVISIONS 4

#ifndef T_THRESHOLD // degrees F
#define T_THRESHOLD 3
#endif

#ifndef P_THRESHOLD // 10^-5 lb/in^2
#define P_THRESHOLD 100
#endif

struct ui_values {
  uint32_t values[NDIVISIONS][NTRIP];
  uint8_t bypass[NDIVISIONS][NTRIP];
  uint8_t trip[NDIVISIONS][NTRIP];
  uint8_t maintenance[NDIVISIONS];
  char display[NLINES][LINELENGTH+1];

  uint8_t actuators[2][NDEV];
};

struct test_state {
  uint32_t test;
  uint32_t test_timer_start;
  uint8_t self_test_running;
  uint8_t self_test_expect;
  uint8_t failed;

  uint8_t test_device_result[2];

  uint8_t test_instrumentation[2];
  uint8_t test_actuation_unit;
  uint8_t test_device;

  uint8_t test_instrumentation_done[4];
  uint8_t test_actuation_unit_done[2];
  uint8_t test_device_done[2];

  uint32_t test_setpoints[4][3];
  uint32_t test_inputs[4][2];

  uint8_t actuation_old_vote;
};

struct core_state {
  struct ui_values ui;
  struct test_state test;
  uint8_t error;
};

int set_display_line(struct ui_values *ui, uint8_t line_number, char *display);
int actuate_devices_generated_C(void);
void core_init(struct core_state *core);
int core_step(struct core_state *core);
char mode_char(uint8_t mode);
char maint_char(uint8_t mode);
int update_ui_instr(struct ui_values *ui);
int update_ui_actuation(struct ui_values *ui);
int update_ui(struct ui_values *ui);
int end_test(struct test_state *test, struct ui_values *ui);
int components_ready(void);
int self_test_timer_expired(struct test_state *test);
int should_start_self_test(struct test_state *test);
int test_step(struct test_state *test, struct ui_values *ui);
#endif // CORE_H_
