#ifndef ACTUATION_H_
#define ACTUATION_H_

#include "stdint.h"

#define _ExtInt(w) char

#define NTRIP 4
#define NDEV 2
#define NCH 3

struct actuation_logic {
    uint8_t vote_actuate[NDEV];
    uint8_t manual_actuate[NDEV];
};

struct manual_actuation_command {
    uint8_t device;
    uint8_t on;
};

uint8_t vote(uint8_t trip_input[NTRIP], uint8_t ch);
uint8_t Voting_Step(uint8_t trip_input[NTRIP]);
#define VOTE_I(_v, _i) (((_v) >> (_i)) & 0x1)

#endif // ACTUATION_H_
