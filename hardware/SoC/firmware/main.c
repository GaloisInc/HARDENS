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
  //printf("\e[s\e[1;1H");//\e[2J");
  for (int line = 0; line < NLINES; ++line) {
    printf("\e[0K");
    printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
  }
  //printf("\e[u");
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
  //printf("\e[%d;1H\e[2K> ", NLINES+1);

  printf("read_rts_command\n");
  static uint8_t dev = 0;
  static uint8_t on = 0;

  cmd->type = ACTUATION_COMMAND;
  cmd->cmd.act.device = dev;
  cmd->cmd.act.on = on;

  int ok = 1;
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
  printf("read_actuation_command\n");
  uint32_t gpio_val = *gpio;
  // TODO: what is cmd->device for?
  cmd->device = id;
  cmd->on = gpio_val & (id+1);
  printf("cmd->device=%u, cmd->on=%u\n",cmd->device,cmd->on);
  return 1;
}

/**
 * Physically set actuator to a new value
 * Platform specific
 */
int send_actuation_command(uint8_t id, struct actuation_command *cmd)
{
  printf("send_actuation_command, id=%u, cmd->device=%u, cmd->on=%u\n",id,cmd->device,cmd->on);
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
    printf("Seeting up GPIO to 0x%X\n",gpio_val);
    *gpio = gpio_val;
    return 0;
  }
  return -1;
}

// Verilog implemented module handlers
int instrumentation_step_handwritten_SystemVerilog(uint8_t div, struct instrumentation_state *state)
{
  // TODO
  return 0;
}

int instrumentation_step_generated_SystemVerilog(uint8_t div, struct instrumentation_state *state)
{
  // TODO
  return 0;
}

int actuation_unit_step_generated_SystemVerilog(uint8_t logic_no, struct actuation_logic *state)
{
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
