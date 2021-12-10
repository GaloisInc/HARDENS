ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

MODEL_DIR=../models
GEN_DIR=generated

ACTUATION_CRY=RTS/Actuation.cry
INSTRUMENTATION_CRY=RTS/Instrumentation.cry

GEN_VOTE_C=${GEN_DIR}/vote.c
GEN_VOTE_INC=${GEN_VOTE_C:.c=.inc.c}
GEN_VOTE_O=${GEN_VOTE_C:.c=.o}

GEN_STEP_TRIP_SIGNALS_C=${GEN_DIR}/step_trip_signals.c
GEN_STEP_TRIP_SIGNALS_INC=${GEN_STEP_TRIP_SIGNALS_C:.c=.inc.c}
GEN_STEP_TRIP_SIGNALS_O=${GEN_STEP_TRIP_SIGNALS_C:.c=.o}


all: actuation.a instrumentation.a core.a

core.a: core.o
	libtool -static -o $@ $^

actuation.a: actuation.o ${GEN_VOTE_O}
	libtool -static -o $@ $^

instrumentation.a: instrumentation.o ${GEN_STEP_TRIP_SIGNALS_O}
	libtool -static -o $@ $^

clean:
	rm -f *.a *.o
	rm -f generated/*.inc.c generated/*.o

proof: ${GEN_VOTE_INC} ${GEN_STEP_TRIP_SIGNALS_INC}
	clang -g -emit-llvm -c ${GEN_VOTE_C} -o ${GEN_DIR}/vote.bc
	clang -g -emit-llvm -c ${GEN_STEP_TRIP_SIGNALS_C} -o ${GEN_DIR}/step_trip_signals.bc

${GEN_VOTE_O}: ${GEN_VOTE_INC}
	clang ${GEN_VOTE_C} -Wall -Wno-shift-op-parentheses -c -o ${GEN_VOTE_O}

${GEN_STEP_TRIP_SIGNALS_O}: ${GEN_STEP_TRIP_SIGNALS_INC}
	clang ${GEN_STEP_TRIP_SIGNALS_C} -Wall -Wno-shift-op-parentheses -c -o ${GEN_STEP_TRIP_SIGNALS_O}

${GEN_VOTE_INC}: ${MODEL_DIR}/${ACTUATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f Coincidence_2_4,Voting_Step ${ACTUATION_CRY} -o ${ROOT_DIR}/${GEN_VOTE_INC}

${GEN_STEP_TRIP_SIGNALS_INC}: ${MODEL_DIR}/${INSTRUMENTATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f Generate_Sensor_Trips,Is_Ch_Tripped ${INSTRUMENTATION_CRY} -o ${ROOT_DIR}/${GEN_STEP_TRIP_SIGNALS_INC}

%.o: %.c
	clang -Wall -I../include $^ -c -o $@
