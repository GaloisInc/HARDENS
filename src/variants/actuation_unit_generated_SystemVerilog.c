#ifdef PLATFORM_HOST
#include "../generated/SystemVerilog/verilator/actuate_d0/VActuate_D0.h"
#include "../generated/SystemVerilog/verilator/actuate_d1/VActuate_D1.h"
#include <stdio.h>
#else
#include "printf.h"
#endif

#define Actuate_D0 Actuate_D0_generated_SystemVerilog
#define Actuate_D1 Actuate_D1_generated_SystemVerilog
#define actuation_unit_step actuation_unit_step_generated_SystemVerilog
#include "../components/actuation_unit.c"

#ifdef PLATFORM_HOST
static VActuate_D0 actuate_d0;
static VActuate_D1 actuate_d1;
uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old) {
    actuate_d0.old = old;
    for(int b = 0; b < 12; ++b) {
        memcpy((uint8_t *)actuate_d0.trips + b, (uint8_t *)trips + (11 - b), 1);
    }
    actuate_d0.eval();
    DEBUG_PRINTF(("<actuation_unit_generated_SystemVerilog.c> actuate_base: device=0x0, old=0x%X, out=0x%X,trips=[",
                old, actuate_d0.out));
    for (int i = 0; i < 3; ++i) {
        DEBUG_PRINTF(("["));
        for (int div = 0; div < 4; ++div) {
        DEBUG_PRINTF(("%u,",trips[i][div]));
        }
        DEBUG_PRINTF(("],"));
    }
    DEBUG_PRINTF(("]\n"));
    return actuate_d0.out;
}

uint8_t Actuate_D1(uint8_t trips[3][4], uint8_t old) {
    actuate_d1.old = old;
    for(int b = 0; b < 12; ++b) {
        memcpy((uint8_t *)actuate_d1.trips + b, (uint8_t *)trips + (11 - b), 1);
    }
    actuate_d1.eval();
    DEBUG_PRINTF(("<actuation_unit_generated_SystemVerilog.c> actuate_base: device=0x1, old=0x%X, out=0x%X,trips=[",
                old, actuate_d1.out));
    for (int i = 0; i < 3; ++i) {
        DEBUG_PRINTF(("["));
        for (int div = 0; div < 4; ++div) {
        DEBUG_PRINTF(("%u,",trips[i][div]));
        }
        DEBUG_PRINTF(("],"));
    }
    DEBUG_PRINTF(("]\n"));
    return actuate_d1.out;
}
#else
#include "bsp.h"
#include "platform.h"

uint8_t actuate_base(uint8_t trips[3][4], uint8_t old, uint8_t id);

uint8_t actuate_base(uint8_t trips[3][4], uint8_t old, uint8_t id)
{
    // NOTE: reverse ordering: 2->1->0 goes to 0->1->2
    // Set value for trip value 0
    size_t idx = 0;
    write_reg(ACTUATION_REG_GENERATED_TRIP_2, (uint32_t) (trips[idx][3] << 24| trips[idx][2] << 16 | trips[idx][1] << 8 | trips[idx][0]));
    idx++;
    write_reg(ACTUATION_REG_GENERATED_TRIP_1, (uint32_t) (trips[idx][3] << 24| trips[idx][2] << 16 | trips[idx][1] << 8 | trips[idx][0]));
    idx++;
    write_reg(ACTUATION_REG_GENERATED_TRIP_0,(uint32_t) (trips[idx][3] << 24| trips[idx][2] << 16 | trips[idx][1] << 8 | trips[idx][0]));

    // trigger the actuation
    // wdata[0] - value of `old` argument
    // wdata[1] - which actuator to actuate
    write_reg(ACTUATION_REG_GENERATED_BASE, (uint32_t)( id << 1 | old));

    // Get actuation results (only the last bit is pertinent for True/false)
    uint8_t res = (uint8_t) (read_reg(ACTUATION_REG_GENERATED_RESULT) & 0x1);

    DEBUG_PRINTF(("<actuation_unit_generated_SystemVerilog.c> actuate_base: device=0x%X, old=0x%X, out=0x%X,trips=[", id, old, res));
    for (int i = 0; i < 3; ++i) {
        DEBUG_PRINTF(("["));
        for (int div = 0; div < 4; ++div) {
        DEBUG_PRINTF(("%u,",trips[i][div]));
        }
        DEBUG_PRINTF(("],"));
    }
    DEBUG_PRINTF(("]\n"));
    return res;
}

uint8_t Actuate_D0(uint8_t trips[3][4], uint8_t old)
{
    return actuate_base(trips, old, 0);
}

uint8_t Actuate_D1(uint8_t trips[3][4], uint8_t old)
{
    return actuate_base(trips, old, 1);
}
#endif
