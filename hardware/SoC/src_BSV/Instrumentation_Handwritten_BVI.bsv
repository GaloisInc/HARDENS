package Instrumentation_Handwritten_BVI;

import Clocks :: *;
import Instrumentation::*;

(* synthesize *)
module mkInstrumentationHandwritten(Instrumentation_IFC);
    ChannelTripped_IFC i_channel <- mkInstrHandwrittenIsChannelTripped();
    SensorTrips_IFC i_sensors <- mkInstrHandwrittenGenerateSensorTrips();

    interface ChannelTripped_IFC channel;
        method is_channel_tripped = i_channel.is_channel_tripped();
    endinterface
    interface SensorTrips_IFC sensors;
        method generate_sensor_trips = i_sensors.generate_sensor_trips();
    endinterface
endmodule

import "BVI" Is_Ch_Tripped_Handwritten =
module mkInstrHandwrittenIsChannelTripped (ChannelTripped_IFC);
    default_clock ();
    default_reset ();

    method out is_channel_tripped (mode, sensor_tripped);
    schedule (is_channel_tripped) CF (is_channel_tripped);
endmodule

import "BVI" Generate_Sensor_Trips_Handwritten =
module mkInstrHandwrittenGenerateSensorTrips (SensorTrips_IFC);
    default_clock ();
    default_reset ();

    method out generate_sensor_trips (vals, setpoints);
    schedule (generate_sensor_trips) CF (generate_sensor_trips);
endmodule

endpackage