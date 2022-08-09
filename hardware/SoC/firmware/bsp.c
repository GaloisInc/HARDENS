#include "bsp.h"
#include "printf.h"

uint32_t i2c_read(uint8_t addr, uint32_t data_tx)
{
  volatile uint32_t *i2c_addr = (void*) I2C_REG_ADDR;
  volatile uint32_t *i2c_data = (void*) I2C_REG_DATA;
  volatile uint32_t *i2c_status = (void*) I2C_REG_STATUS;

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
  uint32_t t_s = time_in_ms()/1000;
  return t_s;
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
  volatile uint32_t *data_rdy = (void*) UART_REG_DATA_READY;
  volatile uint32_t *rx_data = (void*) UART_REG_RX;
  int startime = time_in_ms();
  int delay_ms = 0;
  // Wait 1s for each character
  while ((delay_ms < 2000)) {
    if (*data_rdy){
        return (uint8_t)(*rx_data);
    }
    delay_ms = time_in_ms() - startime;
  }
  return 0;
}

// Read from a register
uint32_t read_reg(uint32_t reg)
{
  uint32_t *p = (void*)reg;
  return *p;
}

// Write `val` to `reg`
void write_reg(uint32_t reg, uint32_t val)
{
  uint32_t *p = (void*)reg;
  *p = val;
}
