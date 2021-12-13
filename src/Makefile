ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

MODEL_DIR=../models
GEN_DIR=generated

ACTUATION_CRY=RTS/Actuation.cry
INSTRUMENTATION_CRY=RTS/Instrumentation.cry

GEN_VOTE_C=${GEN_DIR}/vote.c
GEN_VOTE_INC=${GEN_VOTE_C:.c=.inc.c}

GEN_ACTUATE_DEVICE_C=${GEN_DIR}/actuate_device.c
GEN_ACTUATE_DEVICE_INC=${GEN_ACTUATE_DEVICE_C:.c=.inc.c}

GEN_STEP_TRIP_SIGNALS_C=${GEN_DIR}/step_trip_signals.c
GEN_STEP_TRIP_SIGNALS_INC=${GEN_STEP_TRIP_SIGNALS_C:.c=.inc.c}

SRC=core.c sense_actuate.c actuation_logic.c instrumentation.c actuate.c
C_GEN_SRC=${GEN_VOTE_C} ${GEN_ACTUATE_DEVICE_C} ${GEN_STEP_TRIP_SIGNALS_C}
POSIX_SRC=posix_main.c

OBJ=${SRC:.c=.o}
C_GEN_OBJ=${C_GEN_SRC:.c=.o}
POSIX_OBJ=${POSIX_SRC:.c=.o}


all: posix

clean:
	rm -f rts.posix rts.macos rts.linux
	rm -f *.a *.o
	rm -f generated/*.inc.c generated/*.o generated/*.bc

posix: ${OBJ} ${C_GEN_OBJ} ${POSIX_OBJ}
	clang -fsanitize=address,undefined -g $^ -o rts.posix

linux: posix
	mv rts.posix rts.linux

macos: posix
	mv rts.posix rts.macos

proof: ${GEN_VOTE_INC} ${GEN_STEP_TRIP_SIGNALS_INC}
	clang -g -emit-llvm -c ${GEN_VOTE_C} -o ${GEN_DIR}/vote.bc
	clang -g -emit-llvm -c ${GEN_STEP_TRIP_SIGNALS_C} -o ${GEN_DIR}/step_trip_signals.bc

${GEN_VOTE_INC}: ${MODEL_DIR}/${ACTUATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f Coincidence_2_4,Voting_Step ${ACTUATION_CRY} -o ${ROOT_DIR}/${GEN_VOTE_INC}

${GEN_ACTUATE_DEVICE_INC}: ${MODEL_DIR}/${ACTUATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f ActuateDevice ${ACTUATION_CRY} -o ${ROOT_DIR}/${GEN_ACTUATE_DEVICE_INC}

${GEN_STEP_TRIP_SIGNALS_INC}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f Generate_Sensor_Trips,Is_Ch_Tripped ${INSTRUMENTATION_CRY} -o ${ROOT_DIR}/${GEN_STEP_TRIP_SIGNALS_INC}

%.o: %.inc.c
	clang -g $^ -Wall -I../include -Wno-bitwise-op-parentheses -Wno-unused-function -Wno-shift-op-parentheses -c -o $@

%.o: %.c
	clang -g -Wall -I../include $^ -c -o $@
