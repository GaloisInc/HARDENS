/**
 * Main program entry for RTS
 */
// System includes
#include <stdint.h>
#include <stdlib.h>

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

// GPIO access
volatile uint32_t *gpio = (void*)GPIO_REG;

void update_display()
{
  // This starts printing from the top of the screen
  printf("\e[s\e[1;1H");//\e[2J");
  for (int line = 0; line < NLINES; ++line) {
    printf("\e[0K");
    printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
  }
  printf("\e[u");
}

int read_rts_command(struct rts_command *cmd)
{
  // TODO: make conditional on self-test *not* running
  // printf("Enter command and press enter:\n");
  // char line[256] = {0};
  // for (uint i = 0; i < sizeof(line); i++) {
  //   line[i] = soc_getchar();
  //   if (line[i] == 0 || line[i] == '\n') {
  //     break;
  //   }
  // }
  // printf("You entered: %s\n",line);
  printf("\e[%d;1H\e[2K> ", NLINES+1);

  //printf("read_rts_command\n");
  static uint8_t dev = 0;
  static uint8_t on = 0;

  cmd->type = ACTUATION_COMMAND;
  cmd->cmd.act.device = dev;
  cmd->cmd.act.on = on;

  int ok = 0;
  // TODO: sscanf blows up the binary size
  // hand crafted alternative needed
  return ok;
}

void update_sensors(void)
{
  // TODO
}

/**
 * Read external command, setting *cmd. Does not block.
 * Platform specific
 */
int read_actuation_command(uint8_t id, struct actuation_command *cmd) {
  // TODO: what is cmd->device for?
  cmd->device = id;
  cmd->on = *gpio & (id+1);
  DEBUG_PRINTF(("<main.c> read_actuation_command: cmd->device=%u, cmd->on=%u\n",cmd->device,cmd->on));
  return 1;
}

/**
 * Physically set actuator to a new value
 * Platform specific
 */
int send_actuation_command(uint8_t id, struct actuation_command *cmd)
{
  DEBUG_PRINTF(("<main.c> send_actuation_command, id=%u, cmd->device=%u, cmd->on=%u\n",id,cmd->device,cmd->on));
  // TODO: what is cmd->device for?
  if ((id < 2) && (cmd->on < 2) ) {
    uint32_t gpio_val = *gpio;
    if (id == 0) {
      // Set the actuator bit to zero
      gpio_val = gpio_val & 0xFFFFFFFE;
      // Se the actuator bit to cmd->on value
      gpio_val = gpio_val | cmd->on;
    }
    else {
      // id == 1
      // Set the actuator bit to zero
      gpio_val = gpio_val & 0xFFFFFFFD;
      // Se the actuator bit to cmd->on value
      // Bit shift by one left
      gpio_val = gpio_val | (cmd->on << 1);
    }
    *gpio = gpio_val;
    return 0;
  }
  return -1;
}

// Verilog implemented module handlers
// int instrumentation_step_handwritten_SystemVerilog(uint8_t div, struct instrumentation_state *state)
// {
//   // TODO
//   printf("instrumentation_step_handwritten_SystemVerilog\n");
//   return instrumentation_step(div,state);
// }

// int instrumentation_step_generated_SystemVerilog(uint8_t div, struct instrumentation_state *state)
// {
//   // TODO
//   printf("instrumentation_step_generated_SystemVerilog\n");
//   return instrumentation_step(div,state);
// }

// int actuation_unit_step_generated_SystemVerilog(uint8_t logic_no, struct actuation_logic *state)
// {
//   // TODO
//   printf("actuation_unit_step_generated_SystemVerilog\n");
//   return actuation_unit_step(logic_no, state);
// }

int main(void)
{
  // Prep the screen
  printf("\e[1;1H\e[2J");
  printf("\e[%d;3H\e[2K> ", NLINES+1);

  struct rts_command *cmd = (struct rts_command *)malloc(sizeof(*cmd));
  core_init(&core);
  // TODO: core_id is unused?
  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);
  sense_actuate_init(1, &instrumentation[0], &actuation_logic[0]);

  while (1)
  {
    //update_sensors();
    int retval = core_step(&core);
    DEBUG_PRINTF(("<main.c> core_step= 0x%X\n",retval));
    update_display();
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
  }

  return 0;
}
