#include <stdint.h>
#include "bsp.h"
#include "printf.h"
//
// int main(void)
// {
//     volatile uint32_t *gpio = (void*) GPIO_REG;
//     uint32_t cnt = 0;
//     //char line[256] = {0};
//     //printf("Hello world\n");
//     while(1) {
//         //printf("%u miliseconds passed, GPIO=0x%X\n",time_in_ms(), *gpio);
//         //printf("%d seconds passed...and a sensor reads 0x%X\n",time_in_s(),i2c_read(0x64, 0x0B));

//         // NOTE this is still line buffered
//         //uint8_t c = soc_getchar();
//         //printf(">>>%c<<<\n",c);
//         // for (unsigned int i = 0; i < sizeof(line); i++) {
//         //     line[i] = soc_getchar();
//         //     if (line[i] == 0 || line[i] == '\n') {
//         //     break;
//         //     }
//         // }
//         // printf(">>>%s<<<\n",line);
//         *gpio = cnt;
//         cnt++;
//         cnt = cnt % 256;
//         //delay_ms(1000);
//         delay(100000);
//     }

//     return 0;
// }

int main()
{
	volatile uint32_t *gpio = (void*)GPIO_REG;
    *gpio = 0;
	uint32_t cnt = 0;
	while(1)
	{
		delay_ms(1000);
        if (cnt == 1) {
            cnt = 0;
        } else {
            cnt = 1;
        }
		*gpio = cnt;
        printf("%u miliseconds passed, GPIO=0x%X\n",time_in_ms(), *gpio);
	}
	return 0;
}
