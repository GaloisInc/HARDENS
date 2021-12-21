ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

MODEL_DIR=../models
C_GEN_DIR=generated_csrc
SV_GEN_DIR=generated_vsrc

ACTUATION_CRY=RTS/ActuationUnit.cry
ACTUATOR_CRY=RTS/Actuator.cry
INSTRUMENTATION_CRY=RTS/InstrumentationUnit.cry

GEN_ACTUATION_UNIT_C=${C_GEN_DIR}/actuation_unit.c
GEN_ACTUATION_UNIT_SV=${SV_GEN_DIR}/actuation_unit.sv
GEN_ACTUATION_UNIT_F=Actuate_D0,Actuate_D1

GEN_ACTUATE_ACTUATOR_C=${C_GEN_DIR}/actuate_actuator.c
GEN_ACTUATE_ACTUATOR_SV=${SV_GEN_DIR}/actuate_actuator.sv
GEN_ACTUATE_ACTUATOR_F=ActuateActuator

GEN_STEP_TRIP_SIGNALS_C=${C_GEN_DIR}/step_trip_signals.c
GEN_STEP_TRIP_SIGNALS_SV=${SV_GEN_DIR}/step_trip_signals.sv
GEN_STEP_TRIP_SIGNALS_F=Generate_Sensor_Trips,Is_Ch_Tripped

SRC=core.c sense_actuate.c actuation_logic.c instrumentation.c actuate.c
C_GEN_SRC=${GEN_ACTUATION_UNIT_C} ${GEN_ACTUATE_ACTUATOR_C} ${GEN_STEP_TRIP_SIGNALS_C}
SV_GEN_SRC=${GEN_ACTUATION_UNIT_SV} ${GEN_ACTUATE_ACTUATOR_SV} ${GEN_STEP_TRIP_SIGNALS_SV}
POSIX_SRC=posix_main.c

OBJ=${SRC:.c=.o}
C_GEN_OBJ=${C_GEN_SRC:.c=.o}
POSIX_OBJ=${POSIX_SRC:.c=.o}

VERILATED_INC=$(shell verilator --getenv VERILATOR_ROOT)/include
VERILATED_SRC=$(VERILATED_INC)/verilated.cpp
CVERILOG_FLAGS=--yosys-defaults --little-endian

SV_LIBS=generated_vsrc/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a\
  generated_vsrc/actuate_d0/VActuate_D0__ALL.a\
  generated_vsrc/actuate_d1/VActuate_D1__ALL.a\
  generated_vsrc/is_ch_tripped/VIs_Ch_Tripped__ALL.a\
  generated_vsrc/actuate_actuator/VActuateActuator__ALL.a

VERILATOR_SHIM_OBJS=verilator/instrumentation.o verilator/actuate_d0.o verilator/actuate_d1.o verilator/actuate_actuator.o

# Thanks: https://blog.jgc.org/2007/06/escaping-comma-and-space-in-gnu-make.html
comma := ,

all: rts.posix rts.posix.verilog

clean:
	rm -f rts.posix rts.macos rts.linux
	rm -f *.a *.o
	rm -f verilator/*.o
	rm -f ${C_GEN_DIR}/*.c ${C_GEN_DIR}/*.o ${C_GEN_DIR}/*.bc
	find ${SV_GEN_DIR} -regex '${SV_GEN_DIR}/[^\.]*' -type d -prune -exec rm -r "{}" \;
	rm -f ${SV_GEN_DIR}/*.sv

gen_c: ${C_GEN_SRC}
gen_vlog: ${SV_GEN_SRC}

rts.posix: ${OBJ} ${C_GEN_OBJ} ${POSIX_OBJ}
	clang -fsanitize=address,undefined -g $^ -o rts.posix

rts.posix.verilog: ${OBJ} ${POSIX_OBJ} ${VERILATOR_SHIM_OBJS} ${SV_LIBS}
	clang++ -fsanitize=address,undefined -g $^ -o rts.posix.verilog ${VERILATED_SRC} -I${VERILATED_SRC}/include

linux: rts.posix
	mv rts.posix rts.linux

macos: rts.posix
	mv rts.posix rts.macos

proof: ${GEN_ACTUATION_UNIT_GEN} ${GEN_STEP_TRIP_SIGNALS_INC}
	clang -g -emit-llvm -c ${GEN_ACTUATION_UNIT_C} -o ${C_GEN_DIR}/vote.bc
	clang -g -emit-llvm -c ${GEN_STEP_TRIP_SIGNALS_C} -o ${C_GEN_DIR}/step_trip_signals.bc

ifeq ($(REGEN_SOURCES),1)
${GEN_ACTUATION_UNIT_C}: ${MODEL_DIR}/${ACTUATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_ACTUATION_UNIT_F} ${ACTUATION_CRY} -o ${ROOT_DIR}/${GEN_ACTUATION_UNIT_C}

${GEN_ACTUATION_UNIT_SV}: ${MODEL_DIR}/${ACTUATION_CRY}
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${ACTUATION_CRY} -o ${GEN_ACTUATION_UNIT_SV} \
    ${CVERILOG_FLAGS} \
	--top-level=$(subst $(comma), --top-level=,${GEN_ACTUATION_UNIT_F})

${GEN_ACTUATE_ACTUATOR_C}: ${MODEL_DIR}/${ACTUATOR_CRY}
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_ACTUATE_ACTUATOR_F} ${ACTUATOR_CRY} -o ${ROOT_DIR}/${GEN_ACTUATE_ACTUATOR_C}

${GEN_ACTUATE_ACTUATOR_SV}: ${MODEL_DIR}/${ACTUATOR_CRY}
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${ACTUATOR_CRY} -o ${GEN_ACTUATE_ACTUATOR_SV} \
    ${CVERILOG_FLAGS} \
	--top-level=$(subst $(comma), --top-level=,${GEN_ACTUATE_ACTUATOR_F})

${GEN_STEP_TRIP_SIGNALS_C}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_STEP_TRIP_SIGNALS_F} ${INSTRUMENTATION_CRY} -o ${ROOT_DIR}/${GEN_STEP_TRIP_SIGNALS_C}

${GEN_STEP_TRIP_SIGNALS_SV}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${INSTRUMENTATION_CRY} -o ${GEN_STEP_TRIP_SIGNALS_SV} \
    ${CVERILOG_FLAGS} \
	--top-level=$(subst $(comma), --top-level=,${GEN_STEP_TRIP_SIGNALS_F})
endif

generated_vsrc/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a: ${GEN_STEP_TRIP_SIGNALS_SV}
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Generate_Sensor_Trips $^ \
      -Mdir generated_vsrc/generate_sensor_trips --build

generated_vsrc/is_ch_tripped/VIs_Ch_Tripped__ALL.a: generated_vsrc/step_trip_signals.sv
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Is_Ch_Tripped $^ \
      -Mdir generated_vsrc/is_ch_tripped --build

generated_vsrc/actuate_d0/VActuate_D0__ALL.a: generated_vsrc/actuation_unit.sv
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Actuate_D0 $^ \
      -Mdir generated_vsrc/actuate_d0 --build

generated_vsrc/actuate_d1/VActuate_D1__ALL.a: generated_vsrc/actuation_unit.sv
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Actuate_D1 $^ \
      -Mdir generated_vsrc/actuate_d1 --build

generated_vsrc/actuate_actuator/VActuateActuator__ALL.a: generated_vsrc/actuate_actuator.sv
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module ActuateActuator $^ \
      -Mdir generated_vsrc/actuate_actuator --build

verilator/%.o: verilator/%.cpp ${SV_LIBS}
	clang++ -g -Wall -I../include -Igenerated_vsrc -I${VERILATED_INC} $< -c -o $@

%.o: %.c
	clang -g $^ -Wall -I../include -Wno-bitwise-op-parentheses -Wno-unused-function -Wno-shift-op-parentheses -c -o $@

# %.o: %.c
# 	clang -g -Wall -I../include $^ -c -o $@

# generated_vsrc/svlib.o: generated_vsrc/svlib.cpp
# 	clang++ -g -Wall -I../include -I${VERILATED_INC} $^ -c -o $@
