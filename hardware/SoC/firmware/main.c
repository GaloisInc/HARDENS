/**
 * Main program entry for RTS
 */
// System includes
#include <stdint.h>

// Board includes
#include "bsp.h"
#include "printf.h"

// RTS includes
#include "common.h"
#include "core.h"
#include "instrumentation.h"
#include "actuation_logic.h"
#include "sense_actuate.h"
#include "platform.h"

extern struct instrumentation_state instrumentation[4];

void update_display()
{
  // This starts printing from the top of the screen
  //printf("\e[s\e[1;1H");//\e[2J");
  for (int line = 0; line < NLINES; ++line) {
    printf("\e[0K");
    printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
  }
}

int read_rts_command(struct rts_command *cmd)
{
  printf("Enter command and press enter:\n");
  char line[256] = {0};
  for (uint i = 0; i < sizeof(line); i++) {
    line[i] = soc_getchar();
    if (line[i] == 0 || line[i] == '\n') {
      break;
    }
  }
  printf("You entered: %s\n",line);

  int ok = 0;
  // TODO: sscanf blows up the binary size
  // hand crafted alternative needed
  return ok;
}

void update_sensors(void) {
  // TODO
}

int send_actuation_command(uint8_t id, struct actuation_command *cmd) {
  // TODO
  return 0;
}


int main(void)
{
  struct rts_command *cmd = (struct rts_command *)malloc(sizeof(*cmd));
  core_init(&core);
  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);
  sense_actuate_init(1, &instrumentation[2], &actuation_logic[1]);

  while (1)
  {
    update_sensors();
    core_step(&core);
    update_display();
  }

  return 0;
}
