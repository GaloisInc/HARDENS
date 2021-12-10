#ifndef ACTUATION_H_
#define ACTUATION_H_

#include "stdint.h"
#include "common.h"
#include "instrumentation.h"

#define _ExtInt(w) char

#define NDEV 2
#define NCH 3

struct actuation_logic {
    uint8_t vote_actuate[NDEV];
    uint8_t manual_actuate[NDEV];
};

/* The main logic of the actuation unit */
int actuation_step(uint8_t logic_no, struct actuation_logic *state);

#endif // ACTUATION_H_
