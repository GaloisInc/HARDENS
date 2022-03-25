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
#include "actuation_logic.h"

extern struct instrumentation_state instrumentation[4];

#define CLEAN_SCREEN 1

void update_display()
{
#if CLEAN_SCREEN
  // This starts printing from the top of the screen
  printf("\e[s\e[1;1H");//\e[2J");
#endif
  for (int line = 0; line < NLINES; ++line) {
#if CLEAN_SCREEN
    printf("\e[0K");
#endif
    printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
  }
#if CLEAN_SCREEN
  printf("\e[u");
#endif
}

int read_rts_command(struct rts_command *cmd)
{
  // @todo podhrmic: make conditional on self-test *not* running
  // printf("Enter command and press enter:\n");
  // char line[256] = {0};
  // for (uint i = 0; i < sizeof(line); i++) {
  //   line[i] = soc_getchar();
  //   if (line[i] == 0 || line[i] == '\n') {
  //     break;
  //   }
  // }
  // printf("You entered: %s\n",line);
#if CLEAN_SCREEN
  printf("\e[%d;1H\e[2K> ", NLINES+1);
#endif

  //printf("read_rts_command\n");
  static uint8_t dev = 0;
  static uint8_t on = 0;

  cmd->type = ACTUATION_COMMAND;
  cmd->cmd.act.device = dev;
  cmd->cmd.act.on = on;

  int ok = 0;
  // @todo podhrmic sscanf blows up the binary size
  // hand crafted alternative needed
  return ok;
}

uint32_t get_sensor_data(uint8_t sensor_addr)
{
  uint32_t data = 0;
  uint32_t addr = 0;
  uint32_t result = 0;
  uint8_t intermidiate = 0;

  // run 4 times to get all 32bits of uint32_t value
  for (uint8_t i = 0; i < 4; i++)
  {
    data = i;
    // Set data pointer reg
    write_reg(I2C_REG_DATA, data);
    // Set write addr
    addr = (sensor_addr << 1) | 0x1;
    write_reg(I2C_REG_ADDR, addr);
    // Wait for transaction to finish
    while (read_reg(I2C_REG_STATUS) != 1) {
      ;;
    }
    // Set read addr
    addr = (sensor_addr << 1);
    write_reg(I2C_REG_ADDR, addr);
    // Wait for transaction to finish
    while (read_reg(I2C_REG_STATUS) != 1) {
      ;;
    }
    // Update the result
    intermidiate = read_reg(I2C_REG_DATA);
    result = result | ( intermidiate << i*8);
  }
  return result;
}

void update_sensors(void)
{
  uint32_t val0, val1;
  val0 = get_sensor_data(TEMP_0_I2C_ADDR);
  val1 = get_sensor_data(TEMP_1_I2C_ADDR);
  sensors_demux[0][T][0] = val0;
  sensors_demux[0][T][1] = val1;
  sensors_demux[1][T][0] = val0;
  sensors_demux[1][T][1] = val1;

  val0 = get_sensor_data(PRESSURE_0_I2C_ADDR);
  val1 = get_sensor_data(PRESSURE_1_I2C_ADDR);
  sensors_demux[0][P][0] = val0;
  sensors_demux[0][P][1] = val1;
  sensors_demux[1][P][0] = val0;
  sensors_demux[1][P][1] = val1;
}

/**
 * Read external command, setting *cmd. Does not block.
 * Platform specific
 */
int read_actuation_command(uint8_t id, struct actuation_command *cmd) {
  cmd->device = id;
  cmd->on = (uint8_t) (read_reg(GPIO_REG) & (id+1));
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
  if ((id < 2) && (cmd->on < 2) ) {
    uint32_t gpio_val = read_reg(GPIO_REG);
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
    write_reg(GPIO_REG, gpio_val);
    return 0;
  }
  return -1;
}

int main(void)
{
#if CLEAN_SCREEN
  // Prep the screen
  printf("\e[1;1H\e[2J");
  printf("\e[%d;3H\e[2K> ", NLINES+1);
#endif

  struct rts_command *cmd = (struct rts_command *)malloc(sizeof(*cmd));
  core_init(&core);
  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);
  sense_actuate_init(1, &instrumentation[0], &actuation_logic[0]);

  char line[256];
  while (1)
  {
    update_sensors();
    sprintf(line, "HW ACTUATORS 0x%X", read_reg(GPIO_REG));
    set_display_line(&core.ui, 8, line, 0);
    int retval = core_step(&core);
    DEBUG_PRINTF(("<main.c> core_step= 0x%X\n",retval));
    char line[256];
    sprintf(line, "Uptime: [%u]s\n",time_in_s());
    set_display_line(&core.ui, 9, line, 0);
    update_display();
    sense_actuate_step_0(&instrumentation[0], &actuation_logic[0]);
    sense_actuate_step_1(&instrumentation[2], &actuation_logic[1]);
  }

  return 0;
}
