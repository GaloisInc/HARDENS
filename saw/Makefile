CLANG9 ?= clang
CFLAGS = -g -O1 -I../src/include -Wno-shift-op-precedence

ACTUATION_UNIT_IMPLS=generated/actuation_unit_impl.bc
INSTRUMENTATION_IMPLS=\
  ../src/generated/SystemVerilog/instrumentation_impl.sv\
  ../src/handwritten/SystemVerilog/instrumentation_impl.sv\
  generated/instrumentation_impl.bc \
  handwritten/instrumentation_impl.bc

all: proofs

proofs: instrumentation_proofs actuation_unit_proofs

actuation_unit_proofs: actuation_unit.saw $(ACTUATION_UNIT_IMPLS)
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
	echo "HERE"
	make -C ../src/ $*.c

../src/generated/%.sv:
	make -C ../src/ generated/$*.sv

clean:
	rm -f generated/*.bc
	rm -f handwritten/*.bc
	rm -f *.v

.PHONY: generated/*.sv
FORCE:
