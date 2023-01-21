#   Copyright 2021, 2022, 2023 Galois, Inc.
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.

CLANG9 ?= clang
CFLAGS = -g -O1 -I../src/include -Wno-bitwise-op-parentheses -Wno-shift-op-parentheses

ACTUATOR_IMPLS=generated/actuator_impl.bc
ACTUATION_UNIT_IMPLS=generated/actuation_unit_impl.bc
INSTRUMENTATION_IMPLS=\
  ../src/generated/SystemVerilog/instrumentation_impl.sv\
  ../src/handwritten/SystemVerilog/instrumentation_impl.sv\
  generated/instrumentation_impl.bc \
  handwritten/instrumentation_impl.bc
SATURATION_IMPLS=generated/saturation_impl.bc

all: proofs

proofs: saturation_proofs instrumentation_proofs actuation_unit_proofs actuator_proofs

actuator_proofs: actuator.saw $(ACTUATOR_IMPLS)
	saw $<

actuation_unit_proofs: actuation_unit.saw $(ACTUATION_UNIT_IMPLS)
	saw $<

saturation_proofs: saturation.saw $(SATURATION_IMPLS)
	saw $<

instrumentation_proofs: instrumentation.saw $(INSTRUMENTATION_IMPLS)
	saw $<
	yosys -q -s generated/Is_Ch_Tripped.yosys
	yosys -q -s handwritten/Is_Ch_Tripped.yosys
	yosys -q -s generated/Generate_Sensor_Trips.yosys
	yosys -q -s handwritten/Generate_Sensor_Trips.yosys

generated/%.bc: generated/%.c ../src/generated/C/%.c
	make -C ../src generated/C/$*.c
	$(CLANG9) $(CFLAGS) -o $@ -c $< -emit-llvm

handwritten/%.bc: handwritten/%.c ../src/handwritten/C/%.c
	$(CLANG9) $(CFLAGS) -o $@ -c $< -emit-llvm

../src/generated/SystemVerilog/%.sv: FORCE
	make -C ../src generated/SystemVerilog/$*.sv

../src/%.c:
	make -C ../src/ $*.c

../src/generated/%.sv:
	make -C ../src/ generated/$*.sv

clean:
	rm -f generated/*.bc
	rm -f handwritten/*.bc
	rm -f *.v

.PHONY: generated/*.sv
FORCE:
