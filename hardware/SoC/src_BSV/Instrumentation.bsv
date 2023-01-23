// Copyright 2021, 2022, 2023 Galois, Inc.
// Copyright 2022 Bluespec, Inc.
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

package Instrumentation;

import Vector :: *;

// Instrumentation interface
interface Instrumentation_IFC;
    interface ChannelTripped_IFC channel;
    interface SensorTrips_IFC sensors;
endinterface

// Sub-interface for each implemented function
interface ChannelTripped_IFC;
    (* always_ready *)
    method Bool is_channel_tripped (Bit#(2) mode,
                                    Bool sensor_tripped);
endinterface

interface SensorTrips_IFC;
    (* always_ready *)
    method Bit#(3) generate_sensor_trips (Vector#(3, Bit#(32)) vals,
                                          Vector#(3, Bit#(32)) setpoints);
endinterface

endpackage
