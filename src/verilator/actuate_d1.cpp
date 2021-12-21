#include "actuate_d1/VActuate_D1.h"
#include <stdint.h>

VActuate_D1 actuate_d1;

extern "C"
uint8_t Actuate_D1(uint8_t trips[3][4], uint8_t old) {
    actuate_d1.old = old;
    for(int b = 0; b < 12; ++b) {
        memcpy((uint8_t *)actuate_d1.trips + b, (uint8_t *)trips + (11 - b), 1);
    }
    actuate_d1.eval();
    return actuate_d1.out;
}
