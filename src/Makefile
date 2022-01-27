ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

# Thanks: https://blog.jgc.org/2007/06/escaping-comma-and-space-in-gnu-make.html
comma := ,
space :=

MODEL_DIR=../models
GEN_DIR=generated
HAND_DIR=handwritten
C_DIR=C
SV_DIR=SystemVerilog

C_GEN_DIR=${GEN_DIR}/${C_DIR}
C_HAND_DIR=${HAND_DIR}/${C_DIR}
SV_GEN_DIR=${GEN_DIR}/${SV_DIR}
SV_HAND_DIR=${HAND_DIR}/${SV_DIR}

ACTUATION_CRY=RTS/ActuationUnit.cry
ACTUATOR_CRY=RTS/Actuator.cry
INSTRUMENTATION_CRY=RTS/InstrumentationUnit.cry

GEN_ACTUATION_UNIT_C=${C_GEN_DIR}/actuation_unit_impl.c
GEN_ACTUATION_UNIT_SV=${SV_GEN_DIR}/actuation_unit_impl.sv
GEN_ACTUATION_UNIT_F=Actuate_D0,Actuate_D1
GEN_ACTUATION_UNIT_F_LIST=$(subst $(comma), $(space), $(GEN_ACTUATION_UNIT_F))

GEN_ACTUATE_ACTUATOR_C=${C_GEN_DIR}/actuator_impl.c
GEN_ACTUATE_ACTUATOR_SV=${SV_GEN_DIR}/actuator_impl.sv
GEN_ACTUATE_ACTUATOR_F=ActuateActuator
GEN_ACTUATE_ACTUATOR_F_LIST=$(subst $(comma), $(space), $(GEN_ACTUATE_ACTUATOR_F))

GEN_INSTRUMENTATION_C=${C_GEN_DIR}/instrumentation_impl.c
GEN_INSTRUMENTATION_SV=${SV_GEN_DIR}/instrumentation_impl.sv
GEN_INSTRUMENTATION_F=Generate_Sensor_Trips,Is_Ch_Tripped

GEN_INSTRUMENTATION_F_LIST=$(subst $(comma), $(space), $(GEN_INSTRUMENTATION_F))

GEN_SATURATION_C=${C_GEN_DIR}/saturation_impl.c
GEN_SATURATION_F=Saturation
GEN_SATURATION_F_LIST=$(subst $(comma), $(space), $(GEN_INSTRUMENTATION_F))

C_GEN_SRC=${GEN_ACTUATION_UNIT_C} ${GEN_ACTUATE_ACTUATOR_C} ${GEN_INSTRUMENTATION_C}
SV_GEN_SRC=${GEN_ACTUATION_UNIT_SV} ${GEN_ACTUATE_ACTUATOR_SV} ${GEN_INSTRUMENTATION_SV}
POSIX_SRC=posix_main.c

OBJ=${SRC:.c=.o}
C_GEN_OBJ=${C_GEN_SRC:.c=.o}
POSIX_OBJ=${POSIX_SRC:.c=.o}

VERILATED_INC=$(shell verilator --getenv VERILATOR_ROOT)/include
VERILATED_SRC=$(VERILATED_INC)/verilated.cpp
CVERILOG_FLAGS=--yosys-defaults --little-endian

SV_LIBS=\
  ${SV_GEN_DIR}/verilator/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a\
  ${SV_GEN_DIR}/verilator/is_ch_tripped/VIs_Ch_Tripped__ALL.a\
  ${SV_HAND_DIR}/verilator/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a\
  ${SV_HAND_DIR}/verilator/is_ch_tripped/VIs_Ch_Tripped__ALL.a\
  ${SV_GEN_DIR}/verilator/actuate_d0/VActuate_D0__ALL.a\
  ${SV_GEN_DIR}/verilator/actuate_d1/VActuate_D1__ALL.a\
  ${SV_GEN_DIR}/verilator/actuate_actuator/VActuateActuator__ALL.a

VERILATOR_SHIM_OBJS=\
  verilator/instrumentation_sim.o\
  verilator/actuation_unit_sim.o\
  verilator/actuator_sim.o

SRC=
EXTRA_SRC=

PLATFORM ?= Host

SRC+=\
  core.c \
  sense_actuate.c \
  variants/actuation_unit_generated_C.c \
  variants/actuation_unit_generated_SystemVerilog.c \
  variants/actuator_generated_C.c \
  variants/instrumentation_generated_C.c \
  variants/instrumentation_handwritten_C.c \
  variants/instrumentation_generated_SystemVerilog.c \
  variants/instrumentation_handwritten_SystemVerilog.c \
  variants/saturation_generated_C.c \
  components/instrumentation_common.c

ifeq ($(PLATFORM),Host)
SRC+=posix_main.c
endif

CFLAGS=-Iinclude -g -Wno-shift-op-parentheses -Wno-shift-count-overflow

CC ?= clang
CXX ?= clang++
HW ?= Simulated

SENSORS ?=

ifeq ($(HW),Simulated)
CFLAGS += -DHW_SIMULATOR -I$(VERILATED_INC) -Wno-deprecated
CC = $(CXX)
SRC += $(SV_LIBS)
EXTRA_SRC += $(VERILATED_SRC)
endif

ifeq ($(SENSORS),Simulated)
CFLAGS += -DSIMULATE_SENSORS
endif

$(info BUILD CC=$(CC) HW=$(HW) PLATFORM=$(PLATFORM))

all: rts

rts: $(SRC:.c=.o) $(EXTRA_SRC)
	$(CC) $(CFLAGS) -o $@ $^

variants/%_generated_C.o: variants/%_generated_C.c generated/C/%_impl.c
	$(CC) -c $(CFLAGS) -o $@ $<

variants/%_generated_SystemVerilog.o: variants/%_generated_SystemVerilog.c ${SV_LIBS}
	$(CC) -c $(CFLAGS) -o $@ $<

%.o: %.c
	$(CC) -c $(CFLAGS) -o $@ $<

clean:
	rm -f rts
	rm -rf rts.dSYM
	rm -f ${OBJ}
	rm -f verilator/*.o
	rm -f ${C_GEN_DIR}/*.c ${C_GEN_DIR}/*.o ${C_GEN_DIR}/*.bc
	find ${SV_GEN_DIR} -regex '${SV_GEN_DIR}/[^\.]*' -type d -prune -exec rm -r "{}" \;
	rm -f ${SV_GEN_DIR}/*.sv

rts.posix: ${OBJ} ${POSIX_OBJ}
	clang -fsanitize=address,undefined -g ${CFLAGS} $^ -o rts.posix

linux: rts.posix
	mv rts.posix rts.linux

macos: rts.posix
	mv rts.posix rts.macos

proof: ${GEN_ACTUATION_UNIT_GEN} ${GEN_INSTRUMENTATION_INC}
	clang -g -emit-llvm -c ${GEN_ACTUATION_UNIT_C} -o ${C_GEN_DIR}/vote.bc
	clang -g -emit-llvm -c ${GEN_INSTRUMENTATION_C} -o ${C_GEN_DIR}/step_trip_signals.bc

components/%.generated.C.o: components/%.c
	clang ${CFLAGS} -DSRC=generated -DLANG=C $< -c -o $@

${SV_GEN_DIR}/%.o: ${SV_GEN_DIR}/%.sv

generate_sources: generate_c generate_sv

generate_c: ${GEN_ACTUATION_UNIT_C} ${GEN_ACTUATE_ACTUATOR_C} ${GEN_INSTRUMENTATION_C}
generate_sv: ${GEN_ASVTUATION_UNIT_SV} ${GEN_ASVTUATE_ASVTUATOR_SV} ${GEN_INSTRUMENTATION_SV}

${GEN_SATURATION_C}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	mkdir -p $(dir $@)
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_SATURATION_F} ${INSTRUMENTATION_CRY} -o ${ROOT_DIR}/${GEN_SATURATION_C}

${GEN_ACTUATION_UNIT_C}: ${MODEL_DIR}/${ACTUATION_CRY}
	mkdir -p $(dir $@)
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_ACTUATION_UNIT_F} ${ACTUATION_CRY} -o ${ROOT_DIR}/${GEN_ACTUATION_UNIT_C}

${GEN_ACTUATION_UNIT_SV}: ${MODEL_DIR}/${ACTUATION_CRY}
	mkdir -p $(dir $@)
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${ACTUATION_CRY} -o ${GEN_ACTUATION_UNIT_SV} \
    ${CVERILOG_FLAGS} \
	--top-level=$(subst $(comma), --top-level=,${GEN_ACTUATION_UNIT_F})

${GEN_ACTUATE_ACTUATOR_C}: ${MODEL_DIR}/${ACTUATOR_CRY}
	mkdir -p $(dir $@)
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_ACTUATE_ACTUATOR_F} ${ACTUATOR_CRY} -o ${ROOT_DIR}/${GEN_ACTUATE_ACTUATOR_C}

${GEN_ACTUATE_ACTUATOR_SV}: ${MODEL_DIR}/${ACTUATOR_CRY}
	mkdir -p $(dir $@)
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${ACTUATOR_CRY} -o ${GEN_ACTUATE_ACTUATOR_SV} \
    ${CVERILOG_FLAGS} \
	--top-level=$(subst $(comma), --top-level=,${GEN_ACTUATE_ACTUATOR_F})

${GEN_INSTRUMENTATION_C}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	mkdir -p $(dir $@)
	cd ${MODEL_DIR} && \
		crymp -f ${GEN_INSTRUMENTATION_F} ${INSTRUMENTATION_CRY} -o ${ROOT_DIR}/${GEN_INSTRUMENTATION_C}

${GEN_INSTRUMENTATION_SV}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	mkdir -p $(dir $@)
	CRYPTOLPATH=${MODEL_DIR} \
    cryptol-verilogc ${MODEL_DIR}/${INSTRUMENTATION_CRY} -o ${GEN_INSTRUMENTATION_SV} \
    ${CVERILOG_FLAGS} \
	--top-level=$(subst $(comma), --top-level=,${GEN_INSTRUMENTATION_F})

%/verilator/generate_sensor_trips/VGenerate_Sensor_Trips__ALL.a: %/instrumentation_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Generate_Sensor_Trips $^ \
      -Mdir $*/verilator/generate_sensor_trips --build

%/verilator/is_ch_tripped/VIs_Ch_Tripped__ALL.a: %/instrumentation_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Is_Ch_Tripped $^ \
      -Mdir $*/verilator/is_ch_tripped --build

%/verilator/actuate_d0/VActuate_D0__ALL.a: %/actuation_unit_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Actuate_D0 $^ \
      -Mdir $*/verilator/actuate_d0 --build

%/verilator/actuate_d1/VActuate_D1__ALL.a: %/actuation_unit_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module Actuate_D1 $^ \
      -Mdir $*/verilator/actuate_d1 --build

%/verilator/actuate_actuator/VActuateActuator__ALL.a: %/actuator_impl.sv
	mkdir -p $(dir $@)
	verilator --cc -Wno-WIDTH -Wno-LITENDIAN --top-module ActuateActuator $^ \
      -Mdir $*/verilator/actuate_actuator --build

verilator/%.o: verilator/%.cpp ${SV_LIBS}
	clang++ -g -Wall -Iinclude -Igenerated_vsrc -I${VERILATED_INC} $< -c -o $@
