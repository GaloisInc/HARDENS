#ifdef HW_SIMULATOR
#include "../generated/SystemVerilog/verilator/actuate_d0/VActuate_D0.h"
#include "../generated/SystemVerilog/verilator/actuate_d1/VActuate_D1.h"
#endif

#define Actuate_D0 Actuate_D0_generated_SystemVerilog
#define Actuate_D1 Actuate_D1_generated_SystemVerilog
#define actuation_unit_step actuation_unit_step_generated_SystemVerilog
#include "../components/actuation_unit.c"

#ifdef HW_SIMULATOR
static VActuate_D0 actuate_d0;
static VActuate_D1 actuate_d1;
uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old) {
    actuate_d0.old = old;
    for(int b = 0; b < 12; ++b) {
        memcpy((uint8_t *)actuate_d0.trips + b, (uint8_t *)trips + (11 - b), 1);
    }
    actuate_d0.eval();
    return actuate_d0.out;
}

uint8_t Actuate_D1(uint8_t trips[3][4], uint8_t old) {
    actuate_d1.old = old;
    for(int b = 0; b < 12; ++b) {
        memcpy((uint8_t *)actuate_d1.trips + b, (uint8_t *)trips + (11 - b), 1);
    }
    actuate_d1.eval();
    return actuate_d1.out;
}
#else
uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old)
{
    // Todo
}
#endif
