#include <stdint.h>
#include "bsp.h"
#include "printf.h"

#define GPIO_REG 0x01000000

int main(void)
{
    volatile uint32_t *gpio = (void*) GPIO_REG;
    uint32_t cnt = 0;
    printf("Hello world\n");
    while(1) {
        printf("%u miliseconds passed\n",time_in_ms());
        //printf("%d seconds passed...and a sensor reads 0x%X\n",time_in_s(),i2c_read(0x64, 0x0B));

        // NOTE this is still line buffered
        //uint8_t c = soc_getchar();
        //printf("%c",c);
        *gpio = cnt;
        cnt++;
        delay_ms(1000);
    }

    return 0;
}
