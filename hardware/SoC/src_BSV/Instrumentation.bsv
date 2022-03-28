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