/**
 * Main program entry for RTS
 */
// System includes
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

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

#define CLEAN_SCREEN 0

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

/**
 * Return first space-separated substring
 * TODO: make more robust (effectively we need a custom sscanf)
 */
size_t split_string(size_t in_idx, size_t max_len, char in_array[], char out_array[])
{
  printf(">>>in_array:%s<<<\n",in_array);
  size_t out_idx = in_idx;
  int number_of_bytes = 0;

  for (size_t i = 0; i < max_len; i++) {
    out_array[i] = 0;
  }
  
  for (size_t i = in_idx; i < max_len; i++) {
    if ((in_array[i] == ' ') || (in_array[i] == '\n') || (in_array[i] == '\r') || ((in_array[i] == '\t'))) {
      // check for termination
      if (number_of_bytes == 0) {
        // we just started, continue but increment in_idx
        in_idx++;
        continue;
      } else {
        // we reached the end of segment
        break;
      }
    } else {
      // increment out index
      out_idx++;
      number_of_bytes++;
    }
    memcpy(out_array, &in_array[in_idx], number_of_bytes);
    // terminate string
    in_array[number_of_bytes] = '\n';
  }

  printf(">>>out_array:%s<<<\n",out_array);
  return out_idx;
}

int read_rts_command(struct rts_command *cmd)
{
  char line[256] = {0};
  char substr[256] = {0};
  int ok = 0;

  // @todo podhrmic: make conditional on self-test *not* running
  printf("\nEnter command and press enter:\n");
  delay_ms(1000);

  for (unsigned int i = 0; i < sizeof(line); i++) {
    line[i] = soc_getchar();
    if (line[i] == 0 || line[i] == '\n') {
      break;
    }
  }
  
  printf("> %s\n",line);
#if CLEAN_SCREEN
  printf("\e[%d;1H\e[2K> ", NLINES+1);
#endif

  int index = 2;
  switch (line[0]) {
    case 'A':
      cmd->type = ACTUATION_COMMAND;
      // "A %hhd %hhd", &device, &on
      index = split_string(index, sizeof(line), line, substr);
      cmd->cmd.act.device = atoi(substr);
      split_string(index, sizeof(line), line, substr);
      cmd->cmd.act.on = atoi(substr);
      printf("ACTUATION_COMMAND dev=%d on=%d\n",cmd->cmd.act.device, cmd->cmd.act.on);
      ok = 1;
      break;
    // case 'M':
    //   cmd->type = INSTRUMENTATION_COMMAND;
    //   // "M %hhd %hhd", &div, &on
    //   //split_string(line, sizeof(line), substr);
    //   cmd->instrumentation_division = atoi(substr);
    //   //memcpy(line, substr, sizeof(substr));
    //   cmd->cmd.instrumentation.type = SET_MAINTENANCE;
    //   //split_string(line, sizeof(line), substr);
    //   cmd->cmd.instrumentation.cmd.maintenance.on = atoi(substr);
    //   ok = 1;
    //   break;
    // case 'B':
    //   cmd->type = INSTRUMENTATION_COMMAND;
    //   // "B %hhd %hhd %hhd", &div, &ch, &mode
    //   //split_string(line, sizeof(line), substr);
    //   cmd->instrumentation_division = atoi(substr);
    //   //memcpy(line, substr, sizeof(substr));
    //   cmd->cmd.instrumentation.type = SET_MODE;
    //   //split_string(line, sizeof(line), substr);
    //   cmd->cmd.instrumentation.cmd.mode.channel = atoi(substr);
    //   //memcpy(line, substr, sizeof(substr));
    //   //split_string(line, sizeof(line), substr);
    //   cmd->cmd.instrumentation.cmd.mode.mode_val = atoi(substr);
    //   ok = 1;
    //   break;
    // case 'S':
    //   cmd->type = INSTRUMENTATION_COMMAND;
    //   // "S %hhd %hhd %d", &div, &ch, &val
    //   //split_string(line, sizeof(line), substr);
    //   cmd->instrumentation_division = atoi(substr);
    //   cmd->cmd.instrumentation.type = SET_SETPOINT;
    //   //memcpy(line, substr, sizeof(substr));
    //   //split_string(line, sizeof(line), substr);
    //   cmd->cmd.instrumentation.cmd.setpoint.channel = atoi(substr);
    //   //memcpy(line, substr, sizeof(substr));
    //   //split_string(line, sizeof(line), substr);
    //   cmd->cmd.instrumentation.cmd.setpoint.val = atoi(substr);
    //   ok = 1;
    //   break;
    default:
      break;
  }
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
