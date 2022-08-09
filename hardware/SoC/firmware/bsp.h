#ifndef BSP_H_
#define BSP_H_

#include <stdint.h>
#include "sensors.h"

/**
 * ////////////////////////////////////////////////////////////////
 * Register map
 * ////////////////////////////////////////////////////////////////
 */
#define GPIO_REG                0x01000000

#define UART_REG_TX             0x02000000
#define UART_REG_RX             0x02000004
#define UART_REG_DATA_READY     0x02000008
#define MIN_PRINT_DELAY_TICKS 1000

#define I2C_REG_ADDR            0x03000000
#define I2C_REG_DATA            0x03000004
#define I2C_REG_STATUS          0x03000008

#define TICK_REG_LOW            0x04000000
#define TICK_REG_HIGH           0x04000004

#define INSTRUMENTATION_HANDWRITTEN_REG_BASE 0x05000000
#define INSTRUMENTATION_HANDWRITTEN_REG_INSTR_VAL_0 0x05000004
#define INSTRUMENTATION_HANDWRITTEN_REG_INSTR_VAL_1 0x05000008
#define INSTRUMENTATION_HANDWRITTEN_REG_INSTR_VAL_2 0x0500000C
#define INSTRUMENTATION_HANDWRITTEN_REG_SETPOINT_VAL_0 0x05000010
#define INSTRUMENTATION_HANDWRITTEN_REG_SETPOINT_VAL_1 0x05000014
#define INSTRUMENTATION_HANDWRITTEN_REG_SETPOINT_VAL_2 0x05000018
#define INSTRUMENTATION_HANDWRITTEN_REG_RESULT 0x0500001C

#define INSTRUMENTATION_GENERATED_REG_BASE 0x05000020
#define INSTRUMENTATION_GENERATED_REG_INSTR_VAL_0 0x05000024
#define INSTRUMENTATION_GENERATED_REG_INSTR_VAL_1 0x05000028
#define INSTRUMENTATION_GENERATED_REG_INSTR_VAL_2 0x0500002C
#define INSTRUMENTATION_GENERATED_REG_SETPOINT_VAL_0 0x05000030
#define INSTRUMENTATION_GENERATED_REG_SETPOINT_VAL_1 0x05000034
#define INSTRUMENTATION_GENERATED_REG_SETPOINT_VAL_2 0x05000038
#define INSTRUMENTATION_GENERATED_REG_RESULT 0x0500003C

#define ACTUATION_REG_GENERATED_BASE 0x05000040
#define ACTUATION_REG_GENERATED_TRIP_0 0x05000044
#define ACTUATION_REG_GENERATED_TRIP_1 0x05000048
#define ACTUATION_REG_GENERATED_TRIP_2 0x0500004C
#define ACTUATION_REG_GENERATED_RESULT 0x05000050



/**
 * ////////////////////////////////////////////////////////////////
 * Timing
 * ////////////////////////////////////////////////////////////////
 */
#ifndef CORE_FREQ
#define CORE_FREQ 100000
#endif

#ifndef TICKS_TO_MS_MULTIPLIER
// Should be 1 for FPGA
#define TICKS_TO_MS_MULTIPLIER 3
//#define TICKS_TO_MS_MULTIPLIER 8
#endif

/**
 * ////////////////////////////////////////////////////////////////
 * Function declarations
 * ////////////////////////////////////////////////////////////////
 */
#define min(_a, _b) ((_a) < (_b) ? (_a) : (_b))
#define max(_a, _b) ((_a) > (_b) ? (_a) : (_b))

void delay(uint32_t count);
void delay_ms(uint32_t ms);
uint8_t soc_getchar(void);
uint32_t i2c_read(uint8_t addr, uint32_t data);
uint32_t time_in_s(void);
uint32_t time_in_ms(void);

// Read from a register
uint32_t read_reg(uint32_t reg);

// Write `val` to `reg`
void write_reg(uint32_t reg, uint32_t val);

#endif // BSP_H_
