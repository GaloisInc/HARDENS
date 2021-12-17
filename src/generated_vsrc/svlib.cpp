#include "is_ch_tripped/VIs_Ch_Tripped.h"
#include "generate_sensor_trips/VGenerate_Sensor_Trips.h"
#include "voting_step/VVoting_Step.h"
#include "actuate_device/VActuate_Device.h"
#include <stdint.h>

VIs_Ch_Tripped is_tripped;
VGenerate_Sensor_Trips gen_trips;
VVoting_Step voting_step;
VActuate_Device actuate_device;

extern "C"
uint8_t Actuate_Device(uint8_t vs)
{
    actuate_device.vs = vs;
    actuate_device.eval();
    return actuate_device.out;
}

extern "C"
uint8_t Voting_Step(uint8_t trip_input[4][3])
{
    // This needs to be reversed because the Verilog expects
    // arr[3], arr[2], ...
    // (this is so that the individual _bytes_ have the right direction)
    for(int b = 0; b < 12; ++b) {
        memcpy((uint8_t *)voting_step.inp + b, (uint8_t *)trip_input + (11 - b), 1);
    }
    voting_step.eval();
    return voting_step.out;
}

extern "C"
uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t trip)
{
    is_tripped.mode = mode;
    is_tripped.sensor_tripped = trip;
    is_tripped.eval();
    return is_tripped.out;
}

static uint8_t lookup[8] = { 0x0, 0b100, 0b010, 0b110, 0b001, 0b101, 0b011, 0b111 };

extern "C"
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
