package Instrumentation;

// Instrumentation interface
interface Instrumentation_IFC;
    interface ChannelTripped_IFC channel;
    interface SensorTrips_IFC sensors;
endinterface

// Sub-interface for each implemented function
interface ChannelTripped_IFC;
    (* always_ready *)
    method Bool is_channel_tripped (Bit #(2) mode, Bool sensor_tripped);
endinterface

interface SensorTrips_IFC;
    (* always_ready *)
    // NOTE: this is silly - we should be using arrays, but the docs is not clear
    // about how to use arrays in BVI imports
    method Bit#(3) generate_sensor_trips (Bit#(96) vals, Bit#(96) setpoints);
endinterface

endpackage