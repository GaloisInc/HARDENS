// HARDENS Reactor Trip System (RTS)

// Copyright 2021, 2022, 2023 Galois, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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

void update_display()
{
#if CLEAR_SCREEN
  // This starts printing from the top of the screen
  printf("\e[s\e[1;1H");//\e[2J");
#endif
  for (int line = 0; line < NLINES; ++line) {
#if CLEAR_SCREEN
    printf("\e[0K");
#endif
    printf("%s%s", core.ui.display[line], line == NLINES-1 ? "" : "\n");
  }
#if CLEAR_SCREEN
  printf("\e[u");
#endif
}

int read_rts_command(struct rts_command *cmd)
{
  int ok = 0;
#ifndef ENABLE_SELF_TEST
  const char delimiter[2] = " ";
  char line[254] = {0};
  char *token = NULL;
  int linelen = 0;

  printf("\nEnter command and press enter:\n");
  memset(line,0,sizeof(line));
  for (unsigned int i = 0; i < sizeof(line); i++) {
    line[i] = soc_getchar();
    linelen = i;
    if (line[i] == 0 || line[i] == '\n') {
      break;
    }
  }
  printf(">>>%s<<<[%d]\n",line, linelen);

#if CLEAR_SCREEN
  printf("\e[%d;1H\e[2K> ", NLINES+1);
#endif

  if (linelen < 4) {
    // Too short to be a valid command. "A 1 1\n" is the shortest commnand
    return ok;
  }

  /* get the first token */
  printf("About to call strtok\n");
  token = strtok(line, delimiter);
  printf("strtok called\n");

  if (token != NULL) {
    printf("Command = %s\n",token);
    switch (token[0]) {
      case 'A':
        cmd->type = ACTUATION_COMMAND;
        // "A %hhd %hhd", &device, &on
        token = strtok(NULL, delimiter);
        if (token != NULL) {
          printf("cmd->cmd.act.device = %s\n",token);
          cmd->cmd.act.device = (uint8_t)atoi(token);
          token = strtok(NULL, delimiter);
          if (token != NULL) {
            printf("cmd->cmd.act.on = %s\n",token);
            cmd->cmd.act.on = (uint8_t)atoi(token);
            printf("ACTUATION_COMMAND dev=%u on=%u\n",
                  cmd->cmd.act.device, cmd->cmd.act.on);
            ok = 1;
          }
        }
        break;
      case 'M':
        cmd->type = INSTRUMENTATION_COMMAND;
        cmd->cmd.instrumentation.type = SET_MAINTENANCE;
        // "M %hhd %hhd", &div, &on
        token = strtok(NULL, delimiter);
        if (token != NULL) {
          printf("cmd->instrumentation_division = %s\n",token);
          cmd->instrumentation_division = (uint8_t)atoi(token);
          token = strtok(NULL, delimiter);
          if (token != NULL) {
            printf("cmd->cmd.instrumentation.cmd.maintenance.on = %s\n",token);
            cmd->cmd.instrumentation.cmd.maintenance.on = (uint8_t)atoi(token);
            printf("INSTRUMENTATION_COMMAND MAINTENANCE div=%u on=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.maintenance.on);
            ok = 1;
          }
        }
        break;
      case 'B':
        cmd->type = INSTRUMENTATION_COMMAND;
        cmd->cmd.instrumentation.type = SET_MODE;
        // "B %hhd %hhd %hhd", &div, &ch, &mode
        token = strtok(NULL, delimiter);
        if (token != NULL) {
          printf("cmd->instrumentation_division = %s\n",token);
          cmd->instrumentation_division = (uint8_t)atoi(token);
          token = strtok(NULL, delimiter);
          if (token != NULL) {
            printf("cmd->cmd.instrumentation.cmd.mode.channel = %s\n",token);
            cmd->cmd.instrumentation.cmd.mode.channel = (uint8_t)atoi(token);
            token = strtok(NULL, delimiter);
            if (token != NULL) {
              printf("cmd->cmd.instrumentation.cmd.mode.mode_val = %s\n",token);
              cmd->cmd.instrumentation.cmd.mode.mode_val = (uint8_t)atoi(token);
              printf("INSTRUMENTATION_COMMAND MODE div=%u channel=%u mode=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.mode.channel,
                  cmd->cmd.instrumentation.cmd.mode.mode_val);
              ok = 1;
            }
          }
        }
        break;
      case 'S':
        cmd->type = INSTRUMENTATION_COMMAND;
        cmd->cmd.instrumentation.type = SET_SETPOINT;
        // "S %hhd %hhd %d", &div, &ch, &val
        token = strtok(NULL, delimiter);
        if ((token != NULL) && (token[0] != '\n')) {
          printf("cmd->instrumentation_division = %s\n",token);
          cmd->instrumentation_division = (uint8_t)atoi(token);
          token = strtok(NULL, delimiter);
          if ((token != NULL) && (token[0] != '\n')) {
            printf("cmd->cmd.instrumentation.cmd.setpoint.channel = %s\n",token);
            cmd->cmd.instrumentation.cmd.setpoint.channel = (uint8_t)atoi(token);
            token = strtok(NULL, delimiter);
            if ((token != NULL) && (token[0] != '\n')) {
              printf("cmd->cmd.instrumentation.cmd.setpoint.val = %s\n",token);
              cmd->cmd.instrumentation.cmd.setpoint.val = (uint32_t)atoi(token);
              printf("INSTRUMENTATION_COMMAND SETPOINT div=%u channel=%u val=%u\n",
                  cmd->instrumentation_division,
                  cmd->cmd.instrumentation.cmd.setpoint.channel,
                  cmd->cmd.instrumentation.cmd.setpoint.val);
              ok = 1;
            }
          }
        }
        break;
      default:
        break;
    }
  }
#endif /* #ifndef ENABLE_SELF_TEST */
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
#if CLEAR_SCREEN
  // Prep the screen
  printf("\e[1;1H\e[2J");
  printf("\e[%d;3H\e[2K> ", NLINES+1);
#endif

  //struct rts_command cmd;// = (struct rts_command *)malloc(sizeof(*cmd));
  core_init(&core);
  sense_actuate_init(0, &instrumentation[0], &actuation_logic[0]);
  sense_actuate_init(1, &instrumentation[0], &actuation_logic[0]);

  char line[256];
  while (1)
  {
    //read_rts_command(&cmd);

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
