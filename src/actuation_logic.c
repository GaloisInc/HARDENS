#include "actuation_logic.h"
#include "common.h"
#include "platform.h"

uint8_t Voting_Step(uint8_t trip_input[4][NTRIP], uint8_t old_votes);;
#define VOTE_I(_v, _i) (((_v) >> (_i)) & 0x1)

int
actuation_logic_vote(struct actuation_logic *state)
{
    int err = 0;
    uint8_t trip[4][3];

    err |= read_instrumentation_trip_signals(trip);

    uint8_t old_votes = 0;
    for (int i = 0; i < NDEV; ++i) {
        old_votes |= (state->vote_actuate[i] & 0x1) << i;
    }
    uint8_t votes = Voting_Step(trip, old_votes);

    for (int i = 0; i < NDEV; ++i) {
        state->vote_actuate[i] = VOTE_I(votes, i);
    }

    return err;
}

int
actuation_handle_command(uint8_t logic_no, struct actuation_command *cmd, struct actuation_logic *state)
{
    state->manual_actuate[cmd->device] = cmd->on;
    return 0;
}

int
output_actuation_signals(uint8_t logic_no, struct actuation_logic *state)
{
    int err = 0;
    for (int d = 0; d < NDEV; ++d) {
        uint8_t on = state->vote_actuate[d] || state->manual_actuate[d];
        err |= set_output_actuation_logic(logic_no, d, on);
    }

    return err;
}

int actuation_logic_step(uint8_t logic_no, struct actuation_logic *state)
{
    int err = 0;
    /* Read trip signals & vote */
    err |= actuation_logic_vote(state);

    /* Handle any external commands */
    struct actuation_command cmd;
    int read_cmd = read_actuation_command(logic_no, &cmd);
    if (read_cmd > 0) {
        err |= actuation_handle_command(logic_no, &cmd, state);
    } else if (read_cmd < 0) {
        err |= -read_cmd;
    }

    /* Actuate devices based on voting and commands */
    err |= output_actuation_signals(logic_no, state);
    return err;
}
