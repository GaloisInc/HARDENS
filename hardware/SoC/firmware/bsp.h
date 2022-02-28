#ifndef BSP_H_
#define BSP_H_

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

// Eyeballing the core frequency (ticks per second)
#define CORE_FREQ 100000
// Note this might be different on different machines
#define TICKS_TO_MS_MULTIPLIER 8
#define UART_RX_REG 0x02000004
#define UART_DATA_READY_REG 0x02000008
#define TICK_REG_LOW 0x04000000
#define TICK_REG_HIGH 0x04000004
#define I2C_ADDR_REG 0x03000000
#define I2C_DATA_REG 0x03000004
#define I2C_STATUS_REG 0x03000008

#define min(_a, _b) ((_a) < (_b) ? (_a) : (_b))
#define max(_a, _b) ((_a) > (_b) ? (_a) : (_b))

void delay(uint32_t count);
void delay_ms(uint32_t ms);
uint8_t soc_getchar(void);
uint32_t i2c_read(uint8_t addr, uint32_t data);
uint32_t time_in_s(void);
uint32_t time_in_ms(void);

#endif // BSP_H_
