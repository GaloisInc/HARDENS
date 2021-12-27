#include <stdint.h>

uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3])
{
    uint8_t trips_out = 0;
    for (int i = 0; i < 2; ++i) {
        trips_out |= setpoints[i] < vals[i];
        trips_out <<= 1;
    }
    trips_out |= (int32_t)vals[2] < (int32_t)setpoints[2];

    return trips_out;
}

uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t sensor_tripped)
{
    return (mode == 2) || ((mode == 1) && sensor_tripped);
}
