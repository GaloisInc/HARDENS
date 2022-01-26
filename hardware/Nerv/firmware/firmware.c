#include <stdint.h>
#include <stdio.h>

void delay(uint32_t count);

void delay(uint32_t count)
{
	while(count-->0) {
		__asm__ volatile ("nop");
	}
}
						  
int main(void)
{
	printf("Hello world!");

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
