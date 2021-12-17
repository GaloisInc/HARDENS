ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

MODEL_DIR=../models
C_GEN_DIR=generated_csrc
SV_GEN_DIR=generated_vsrc

ACTUATION_CRY=RTS/Actuation.cry
INSTRUMENTATION_CRY=RTS/Instrumentation.cry

GEN_VOTE_C=${C_GEN_DIR}/vote.c
GEN_VOTE_SV=${SV_GEN_DIR}/vote.sv
GEN_VOTE_INC=${GEN_VOTE_C:.c=.inc.c}
GEN_VOTE_F=Coincidence_2_4,Voting_Step

GEN_ACTUATE_DEVICE_C=${C_GEN_DIR}/actuate_device.c
GEN_ACTUATE_DEVICE_SV=${SV_GEN_DIR}/actuate_device.sv
GEN_ACTUATE_DEVICE_INC=${GEN_ACTUATE_DEVICE_C:.c=.inc.c}
GEN_ACTUATE_DEVICE_F=Actuate_Device

GEN_STEP_TRIP_SIGNALS_C=${C_GEN_DIR}/step_trip_signals.c
GEN_STEP_TRIP_SIGNALS_SV=${SV_GEN_DIR}/step_trip_signals.sv
GEN_STEP_TRIP_SIGNALS_INC=${GEN_STEP_TRIP_SIGNALS_C:.c=.inc.c}
GEN_STEP_TRIP_SIGNALS_F=Generate_Sensor_Trips,Is_Ch_Tripped

SRC=core.c sense_actuate.c actuation_logic.c instrumentation.c actuate.c
C_GEN_SRC=${GEN_VOTE_C} ${GEN_ACTUATE_DEVICE_C} ${GEN_STEP_TRIP_SIGNALS_C}
SV_GEN_SRC=${GEN_VOTE_SV} ${GEN_ACTUATE_DEVICE_SV} ${GEN_STEP_TRIP_SIGNALS_SV}
POSIX_SRC=posix_main.c

OBJ=${SRC:.c=.o}
C_GEN_OBJ=${C_GEN_SRC:.c=.o}
POSIX_OBJ=${POSIX_SRC:.c=.o}

VERILATED_INC=$(shell verilator --getenv VERILATOR_ROOT)/include
VERILATED_SRC=$(VERILATED_INC)/verilated.cpp
CVERILOG_FLAGS=--yosys-defaults --little-endian

SV_LIBS=generated_vsrc/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a\
  generated_vsrc/voting_step/VVoting_Step__ALL.a\
  generated_vsrc/is_ch_tripped/VIs_Ch_Tripped__ALL.a\
  generated_vsrc/actuate_device/Vactuate_device__ALL.a

# Thanks: https://blog.jgc.org/2007/06/escaping-comma-and-space-in-gnu-make.html
comma := ,

all: rts.posix

clean:
	rm -f rts.posix rts.macos rts.linux
	rm -f *.a *.o
	rm -f ${C_GEN_DIR}/*.inc.c ${C_GEN_DIR}/*.o ${C_GEN_DIR}/*.bc
	rm -f ${SV_GEN_DIR}/*.sv

gen_c: ${C_GEN_SRC:.c=.inc.c}
gen_vlog: ${SV_GEN_SRC}

rts.posix: ${OBJ} ${C_GEN_OBJ} ${POSIX_OBJ}
	clang -fsanitize=address,undefined -g $^ -o rts.posix

rts.posix.verilog: ${OBJ} ${POSIX_OBJ} ${SV_LIBS} generated_vsrc/svlib.o generated_vsrc/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a
	clang++ -fsanitize=address,undefined -g $^ -o rts.posix.verilog ${VERILATED_SRC} -I${VERILATED_SRC}/include

linux: rts.posix
	mv rts.posix rts.linux

macos: rts.posix
	mv rts.posix rts.macos

proof: ${GEN_VOTE_INC} ${GEN_STEP_TRIP_SIGNALS_INC}
	clang -g -emit-llvm -c ${GEN_VOTE_C} -o ${C_GEN_DIR}/vote.bc
	clang -g -emit-llvm -c ${GEN_STEP_TRIP_SIGNALS_C} -o ${C_GEN_DIR}/step_trip_signals.bc

${GEN_VOTE_INC}: ${MODEL_DIR}/${ACTUATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_VOTE_F} ${ACTUATION_CRY} -o ${ROOT_DIR}/${GEN_VOTE_INC}

${GEN_VOTE_SV}: ${MODEL_DIR}/${ACTUATION_CRY}
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${ACTUATION_CRY} -o ${GEN_VOTE_SV} \
    ${CVERILOG_FLAGS} \
	--top-level=$(subst $(comma), --top-level=,${GEN_VOTE_F})

${GEN_ACTUATE_DEVICE_INC}: ${MODEL_DIR}/${ACTUATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_ACTUATE_DEVICE_F} ${ACTUATION_CRY} -o ${ROOT_DIR}/${GEN_ACTUATE_DEVICE_INC}

${GEN_ACTUATE_DEVICE_SV}: ${MODEL_DIR}/${ACTUATION_CRY}
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${ACTUATION_CRY} -o ${GEN_ACTUATE_DEVICE_SV} \
    ${CVERILOG_FLAGS} \
	--top-level=$(subst $(comma), --top-level=,${GEN_ACTUATE_DEVICE_F})

${GEN_STEP_TRIP_SIGNALS_INC}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_STEP_TRIP_SIGNALS_F} ${INSTRUMENTATION_CRY} -o ${ROOT_DIR}/${GEN_STEP_TRIP_SIGNALS_INC}

${GEN_STEP_TRIP_SIGNALS_SV}: ${MODEL_DIR}/${ACTUATION_CRY}
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${ACTUATION_CRY} -o ${GEN_STEP_TRIP_SIGNALS_SV} \
    ${CVERILOG_FLAGS} \
	--top-level=$(subst $(comma), --top-level=,${GEN_STEP_TRIP_SIGNALS_F})

generated_vsrc/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a: generated_vsrc/step_trip_signals.sv
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Generate_Sensor_Trips $^ \
      -Mdir generated_vsrc/generate_sensor_trips --build

generated_vsrc/is_ch_tripped/VIs_Ch_Tripped__ALL.a: generated_vsrc/step_trip_signals.sv
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Is_Ch_Tripped $^ \
      -Mdir generated_vsrc/is_ch_tripped --build

generated_vsrc/voting_step/VVoting_Step__ALL.a: generated_vsrc/vote.sv
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Voting_Step $^ \
      -Mdir generated_vsrc/voting_step --build

generated_vsrc/actuate_device/Vactuate_device__ALL.a: generated_vsrc/actuate_device.sv
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Actuate_Device $^ \
      -Mdir generated_vsrc/actuate_device --build

%.o: %.inc.c
	clang -g $^ -Wall -I../include -Wno-bitwise-op-parentheses -Wno-unused-function -Wno-shift-op-parentheses -c -o $@

%.o: %.c
	clang -g -Wall -I../include $^ -c -o $@

generated_vsrc/svlib.o: generated_vsrc/svlib.cpp
	clang++ -g -Wall -I../include -I${VERILATED_INC} $^ -c -o $@
