#include "actuation.h"
#include "common.h"
#include "platform.h"

uint8_t vote(uint8_t trip_input[4][NTRIP], uint8_t ch);
uint8_t Voting_Step(uint8_t trip_input[4][NTRIP]);
#define VOTE_I(_v, _i) (((_v) >> (_i)) & 0x1)

int
actuation_logic_step(struct actuation_logic *state)
{
    int err = 0;
    uint8_t trip[4][3];

    err = read_trip_signals(trip);
    if(err) return err;

    uint8_t votes = Voting_Step(trip);

    for (int i = 0; i < NDEV; ++i) {
        state->vote_actuate[i] = VOTE_I(votes, i);
    }

    return err;
}

int
actuation_handle_command(uint8_t logic_no, struct actuation_logic *state)
{
    struct actuation_command cmd;
    int err = read_actuation_command(logic_no, &cmd);
    if (err > 0) {
        state->manual_actuate[cmd.device] = cmd.on;
    }

    return 0;
}

int
actuate_devices(uint8_t logic_no, struct actuation_logic *state)
{
    int err = 0;
    for (int d = 0; d < NDEV; ++d) {
        uint8_t on = state->vote_actuate[d] || state->manual_actuate[d];
        // @abakst if it's a problem to actuate "on"
        // repeatedly then we just need to track this state in the
        // actuation logic struct.
        err |= actuate_device(logic_no, d, on);
    }

    return err;
}

int actuation_step(uint8_t logic_no, struct actuation_logic *state)
{
    int err = 0;
    /* Read trip signals & vote */
    err = actuation_logic_step(state);
    if(err) return err;

    /* Handle any external commands */
    err = actuation_handle_command(logic_no, state);
    if(err) return err;

    /* Actuate devices based on voting and commands */
    err = actuate_devices(logic_no, state);
    return err;
}
