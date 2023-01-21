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

To run the proofs, just run `make proofs`.

## Dependencies

- SAW 0.9 <https://saw.galois.com>,

- SAW depends on `clang 9` (`10` _may_ work, but is untested). If `clang` in your
  path is a different version, you will need to install `clang 9` and supply the
  executable in the `CLANG9` environment variable, i.e.
  `CLANG9=/path/to/bin/clang9 make proofs`.

## License

   Copyright 2021, 2022, 2023 Galois, Inc.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
