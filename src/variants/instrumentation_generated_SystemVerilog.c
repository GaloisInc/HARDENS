#ifdef PLATFORM_HOST
#include "../generated/SystemVerilog/verilator/generate_sensor_trips/VGenerate_Sensor_Trips.h"
#include "../generated/SystemVerilog/verilator/is_ch_tripped/VIs_Ch_Tripped.h"
#include <stdio.h>
#else
#include "printf.h"
#endif

#define Generate_Sensor_Trips Generate_Sensor_Trips_generated_SystemVerilog
#define Is_Ch_Tripped Is_Ch_Tripped_generated_SystemVerilog
#define instrumentation_step instrumentation_step_generated_SystemVerilog
#include "../components/instrumentation.c"

#ifdef PLATFORM_HOST
static VIs_Ch_Tripped is_tripped;
static VGenerate_Sensor_Trips gen_trips;

uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t trip)
{
    is_tripped.mode = mode;
    is_tripped.sensor_tripped = trip;
    is_tripped.eval();
    return is_tripped.out;
}

static uint8_t lookup[8] = { 0x0, 0b100, 0b010, 0b110, 0b001, 0b101, 0b011, 0b111 };

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
    write_reg(INSTRUMENTATION_GENERATED_REG_BASE, val);
    uint32_t res = read_reg(INSTRUMENTATION_GENERATED_REG_RESULT);
    DEBUG_PRINTF(("<instrumentation_generated_SystemVerilog.c> Is_Ch_Tripped: base=0x%X, res=0x%X\n",val,res));
    return (uint8_t)(res & 0x3);
}

uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3])
{
    // Set value for setpoints
    write_reg(INSTRUMENTATION_GENERATED_REG_SETPOINT_VAL_0, setpoints[0]);
    write_reg(INSTRUMENTATION_GENERATED_REG_SETPOINT_VAL_1, setpoints[1]);
    write_reg(INSTRUMENTATION_GENERATED_REG_SETPOINT_VAL_2, setpoints[2]);
    write_reg(INSTRUMENTATION_GENERATED_REG_INSTR_VAL_0, vals[0]);
    write_reg(INSTRUMENTATION_GENERATED_REG_INSTR_VAL_1, vals[1]);
    write_reg(INSTRUMENTATION_GENERATED_REG_INSTR_VAL_2, vals[2]);
    write_reg(INSTRUMENTATION_GENERATED_REG_BASE, 0x1);
    uint32_t res = read_reg(INSTRUMENTATION_GENERATED_REG_RESULT);
    DEBUG_PRINTF(("<instrumentation_generated_SystemVerilog.c> Generate_Sensor_Trips: vals=[%u,%u,%u], setpoints=[%u,%u,%u], res=0x%X\n",vals[0],vals[1],vals[2],setpoints[0],setpoints[1],setpoints[2],res));
    return (uint8_t) (res & 0xFF);
}
#endif
