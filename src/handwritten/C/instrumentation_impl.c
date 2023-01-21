// HARDENS Reactor Trip System (RTS)

// Copyright 2021, 2022, 2023 Galois, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <stdint.h>

// Identified by SAW: vals[2] and setpoints[2] must be less than 0x80000000
uint8_t Generate_Sensor_Trips(uint32_t vals[3], uint32_t setpoints[3])
{
    uint8_t trips_out = 0;
    trips_out |= Trip(vals, setpoints, 0);
    //@ assert trips_out <= 0x1;
    trips_out |= (Trip(vals, setpoints, 1) << 1);
    //@ assert trips_out <= 0x3;
    trips_out |= (Trip(vals, setpoints, 2) << 2);

    return trips_out;
}

uint8_t Trip(uint32_t vals[3], uint32_t setpoints[3], uint8_t ch)
{
    if (ch <= 1) {
        return (setpoints[ch] < vals[ch]);
    } else {
        return ((int32_t)vals[ch] < (int32_t)setpoints[ch]);
    }
}

uint8_t Is_Ch_Tripped(uint8_t mode, uint8_t sensor_tripped)
{
    return (mode == 2) || ((mode == 1) && sensor_tripped);
}
