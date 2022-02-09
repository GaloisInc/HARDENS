#include <stdint.h>
#include <stdio.h>

#define UART_RX_REG 0x02000004
#define UART_DATA_READY_REG 0x02000008

void delay(uint32_t count);

void delay(uint32_t count)
{
	while(count-->0) {
		__asm__ volatile ("nop");
	}
}
						  
int main(void)
{
	volatile uint32_t *data_rdy = (void*) UART_DATA_READY_REG;
	volatile uint32_t *rx_data = (void*) UART_RX_REG;
	printf("Hello world!\n");
	delay(100);

	while(1) {
		if (*data_rdy){
			printf("%c", *rx_data);
		}
	}

	// // Uncomment for a loop print
	// volatile uint32_t *leds = (void*)0x01000000;
	// *leds = 0;
	// uint32_t cnt = 0;
	// while(1)
	// {
	// 	delay(500000);
	// 	*leds = cnt++;
	// 	printf("%d: Still alive!",cnt);
	// }

	return 0;
}
