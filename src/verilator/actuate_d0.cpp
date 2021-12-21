#include "actuate_d0/VActuate_D0.h"
#include <stdint.h>

VActuate_D0 actuate_d0;

extern "C"
uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old) {
    actuate_d0.old = old;
    for(int b = 0; b < 12; ++b) {
        memcpy((uint8_t *)actuate_d0.trips + b, (uint8_t *)trips + (11 - b), 1);
    }
    actuate_d0.eval();
    return actuate_d0.out;
}
