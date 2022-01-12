# SAW Correctness Proofs

The scripts in this directory establish correctness for specific components
derived from the Cryptol executable model. These correspond to the components
under the [handwritten](../src/handwritten) and [generated](../src/generated)
source directories.

Currently, these scripts establish correctness of implementations of:

- `RTS::Actuator::ActuateActuator` (C)
- `RTS::ActuationUnit::Actuate_D0` (C)
- `RTS::ActuationUnit::Actuate_D1` (C)
- `RTS::InstrumentationUnit::Is_Ch_Tripped` (C and SystemVerilog)
- `RTS::InstrumentationUnit::Generate_Sensor_Trips` (C and SystemVerilog)

The C proofs are entirely within SAW. The SystemVerilog proofs use SAW to
extract a Verilog implementation from the Cryptol model, and then use a `yosys`
to establish equivalence (e.g. see [](generated/Is_Ch_Tripped.yosys)).
