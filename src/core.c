#include "core.h"
#include "platform.h"
#include "stdio.h"

#define INST_OFFSET 0
#define ACT_OFFSET 5
char INSTR_LINE_FMT[] = "#I %d (%c): T[%5d %c %d] P[%5d %c %d] S[%5d %c %d]";
char ACT_LINE_FMT[] = "#A %d [%d %d]";

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
             mode_char(ui->bypass[i][T]), ui->trip[i][T], ui->values[i][P],
             mode_char(ui->bypass[i][P]), ui->trip[i][P], ui->values[i][S],
             mode_char(ui->bypass[i][S]), ui->trip[i][S]);

    set_display_line(i, line, sizeof(line));
  }

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
    set_display_line(ACT_OFFSET + i, line, sizeof(line));
  }

  return err;
}

int update_ui(struct ui_values *ui) {
  int err = 0;
  err |= update_ui_instr(ui);
  err |= update_ui_actuation(ui);

  return err;
}

int core_step(struct ui_values *ui) {
  int err = 0;
  struct rts_command rts;

  err |= update_ui(ui);

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

  // Self Test

  return err;
}
