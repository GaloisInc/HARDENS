#include "bsp.h"

uint32_t i2c_read(uint8_t addr, uint32_t data_tx)
{
  volatile uint32_t *i2c_addr = (void*) I2C_ADDR_REG;
  volatile uint32_t *i2c_data = (void*) I2C_DATA_REG;
  volatile uint32_t *i2c_status = (void*) I2C_STATUS_REG;

  // First set data
  *i2c_data = data_tx;
  // Second set address
  *i2c_addr = addr;
  // Now the transaction is initialized, so wait for completion
  delay(100);
  while (1) {
    uint32_t status = *i2c_status;
    if (status) {
      // Return the acquired data
      uint32_t data = *i2c_data;
      return data;
    }
    delay(1000);
  }
}

uint32_t time_in_s(void)
{
  volatile uint32_t *tick_reg_low = (void*) TICK_REG_LOW;
  volatile uint32_t *tick_reg_high = (void*) TICK_REG_HIGH;
  uint64_t ticks = (uint64_t) (*tick_reg_high << 31 | *tick_reg_low);
  return (uint32_t)((ticks)/CORE_FREQ);
}

uint32_t time_in_ms(void)
{
  volatile uint32_t *tick_reg_low = (void*) TICK_REG_LOW;
  volatile uint32_t *tick_reg_high = (void*) TICK_REG_HIGH;
  uint64_t ticks = (uint64_t) (*tick_reg_high << 31 | *tick_reg_low);
  return (uint32_t)((ticks*1000)/(CORE_FREQ*TICKS_TO_MS_MULTIPLIER));
}

void delay_ms(uint32_t ms)
{
    uint32_t ticks = ms*CORE_FREQ/1000;
    delay(ticks);
}

void delay(uint32_t count)
{
	while(count-->0) {
		__asm__ volatile ("nop");
	}
}

uint8_t soc_getchar(void)
{
  volatile uint32_t *data_rdy = (void*) UART_DATA_READY_REG;
  volatile uint32_t *rx_data = (void*) UART_RX_REG;
  while (1) {
    if (*data_rdy){
        return (uint8_t)(*rx_data);
    }
  }
}

