#ifdef PLATFORM_HOST
#include "../handwritten/SystemVerilog/verilator/generate_sensor_trips/VGenerate_Sensor_Trips.h"
#include "../handwritten/SystemVerilog/verilator/is_ch_tripped/VIs_Ch_Tripped.h"
#include <stdio.h>
#else
#include "printf.h"
#endif

#define Generate_Sensor_Trips Generate_Sensor_Trips_handwritten_SystemVerilog
#define Is_Ch_Tripped Is_Ch_Tripped_handwritten_SystemVerilog
#define instrumentation_step instrumentation_step_handwritten_SystemVerilog
#include "../components/instrumentation.c"

static uint8_t lookup[8] = { 0x0, 0b100, 0b010, 0b110, 0b001, 0b101, 0b011, 0b111 };

#ifdef PLATFORM_HOST
static VIs_Ch_Tripped is_tripped;
static VGenerate_Sensor_Trips gen_trips;

uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t trip)
{
    is_tripped.mode = mode;
    is_tripped.sensor_tripped = trip;
    is_tripped.eval();
    uint32_t val = (trip & 0x1) << 3| (mode & 0x3) << 1| 0x0;
    DEBUG_PRINTF(("<instrumentation_handwritten_SystemVerilog.c> Is_Ch_Tripped: mode=0x%X, trip=0x%X, base=0x%X, res=0x%X\n",
    mode, trip, val,is_tripped.out));
    return is_tripped.out;
}

uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3])
{
    gen_trips.vals[0] = vals[2];
    gen_trips.vals[1] = vals[1];
    gen_trips.vals[2] = vals[0];
    gen_trips.setpoints[0] = setpoints[2];
    gen_trips.setpoints[1] = setpoints[1];
    gen_trips.setpoints[2] = setpoints[0];
    gen_trips.eval();
    uint8_t out = gen_trips.out;
    DEBUG_PRINTF(("<instrumentation_handwritten_SystemVerilog.c> Generate_Sensor_Trips:  vals=[%u,%u,%u], setpoints=[%u,%u,%u], lookup[%d]=0x%X\n",
    vals[0],vals[1],vals[2],setpoints[0],setpoints[1],setpoints[2],out,lookup[out]));
    return lookup[out];
}
#else
#include "bsp.h"
#include "platform.h"

uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t trip)
{
    // wdata[0] - fnc select ( 0 - is_channel_tripped | 1 - generate_sensor_trips)
    // wdata[2:1] - mode
    // wdata[3] - sensor_tripped
    // rg_instr_hand_res[2:0] - result
    // rg_instr_hand_res[31] - fnc select ( 0 - is_channel_tripped | 1 - generate_sensor_trips)
    uint32_t val = (trip & 0x1) << 3| (mode & 0x3) << 1| 0x0;
    write_reg(INSTRUMENTATION_HANDWRITTEN_REG_BASE, val);
    uint8_t res = (uint8_t)(read_reg(INSTRUMENTATION_HANDWRITTEN_REG_RESULT) & 0x1);
    DEBUG_PRINTF(("<instrumentation_handwritten_SystemVerilog.c> Is_Ch_Tripped: mode=0x%X, trip=0x%X, base=0x%X, res=0x%X\n",
    mode, trip, val,res));
    return res;
}

uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3])
{
    // Set value for setpoints
    write_reg(INSTRUMENTATION_HANDWRITTEN_REG_SETPOINT_VAL_0, setpoints[0]);
    write_reg(INSTRUMENTATION_HANDWRITTEN_REG_SETPOINT_VAL_1, setpoints[1]);
    write_reg(INSTRUMENTATION_HANDWRITTEN_REG_SETPOINT_VAL_2, setpoints[2]);
    write_reg(INSTRUMENTATION_HANDWRITTEN_REG_INSTR_VAL_0, vals[0]);
    write_reg(INSTRUMENTATION_HANDWRITTEN_REG_INSTR_VAL_1, vals[1]);
    write_reg(INSTRUMENTATION_HANDWRITTEN_REG_INSTR_VAL_2, vals[2]);
    write_reg(INSTRUMENTATION_HANDWRITTEN_REG_BASE, 0x1);
    uint8_t out = (uint8_t)(read_reg(INSTRUMENTATION_HANDWRITTEN_REG_RESULT) & 0x7);
    DEBUG_PRINTF(("<instrumentation_handwritten_SystemVerilog.c> Generate_Sensor_Trips: vals=[%u,%u,%u], setpoints=[%u,%u,%u], lookup[%d]=0x%X\n"
    ,vals[0],vals[1],vals[2],setpoints[0],setpoints[1],setpoints[2],out,lookup[out]));
    return lookup[out];
}

#endif
