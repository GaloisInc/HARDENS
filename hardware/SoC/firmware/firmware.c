#include <stdint.h>
#include <stdio.h>
#include "bsp.h"

						  
int main(void)
{
	printf("Hello world\n");
	while(1) {
		printf("%d miliseconds passed\n",time_in_ms());
		//printf("%d seconds passed...and a sensor reads 0x%X\n",time_in_s(),i2c_read(0x64, 0x0B));

		// NOTE this is still line buffered
		//uint8_t c = soc_getchar();
		//printf("%c",c);
		delay_ms(1000);
	}

	return 0;
}
