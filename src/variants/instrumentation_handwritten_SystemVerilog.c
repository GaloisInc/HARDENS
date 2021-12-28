#ifdef HW_SIMULATOR
#include "../handwritten/SystemVerilog/verilator/generate_sensor_trips/VGenerate_Sensor_Trips.h"
#include "../handwritten/SystemVerilog/verilator/is_ch_tripped/VIs_Ch_Tripped.h"
#endif

#define Generate_Sensor_Trips Generate_Sensor_Trips_handwritten_SystemVerilog
#define Is_Ch_Tripped Is_Ch_Tripped_handwritten_SystemVerilog
#define instrumentation_step instrumentation_step_handwritten_SystemVerilog
#include "../components/instrumentation.c"

#ifdef HW_SIMULATOR
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
#endif
