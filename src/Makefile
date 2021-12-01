ROOT_DIR:=$(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

MODEL_DIR=../models
GEN_DIR=generated
ACTUATION_CRY=RTS/Actuation.cry
GEN_VOTE_INC=${GEN_DIR}/vote.inc.c
GEN_VOTE_C=${GEN_DIR}/vote.c
GEN_VOTE_O=${GEN_VOTE_C:.c=.o}

all: actuation.a

actuation.a: actuation.o ${GEN_VOTE_O}
	libtool -static -o $@ $^

clean:
	rm -f *.a *.o
	rm -f generated/*.inc.c generated/*.o

proof: ${GEN_VOTE_INC}
	clang -emit-llvm -c ${GEN_VOTE_C} -o ${GEN_DIR}/vote.bc

${GEN_VOTE_O}: ${GEN_VOTE_INC}
	clang ${GEN_VOTE_C} -Wno-shift-op-parentheses -c -o ${GEN_VOTE_O}

${GEN_VOTE_INC}: ${MODEL_DIR}/${ACTUATION_CRY}
	cd ${MODEL_DIR} && \
		crymp -f Coincidence_2_4,Voting_Step RTS/Actuation.cry -o ${ROOT_DIR}/${GEN_VOTE_INC}

actuation.o: actuation.c
	clang -I../include $^ -c -o $@
