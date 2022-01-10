#include "common.h"
#include "platform.h"
#include "actuation_logic.h"

#define VOTE_I(_v, _i) (((_v) >> (_i)) & 0x1)

/*@requires \valid(state);
  @requires \valid(state->vote_actuate+(0..1));
  @assigns *state;
*/
static int
actuation_logic_vote(struct actuation_logic *state)
{
    int err = 0;
    uint8_t trip[3][4];

    err |= read_instrumentation_trip_signals(trip);

    state->vote_actuate[0] = Actuate_D0(trip, state->vote_actuate[0] != 0);
    state->vote_actuate[1] = Actuate_D1(trip, state->vote_actuate[1] != 0);

    return err;
}

static int
actuation_handle_command(uint8_t logic_no, struct actuation_command *cmd, struct actuation_logic *state)
{
    state->manual_actuate[cmd->device] = cmd->on;
    return 0;
}

static int
output_actuation_signals(uint8_t logic_no, struct actuation_logic *state)
{
    int err = 0;
    for (int d = 0; d < NDEV; ++d) {
        uint8_t on = state->vote_actuate[d] || state->manual_actuate[d];
        err |= set_output_actuation_logic(logic_no, d, on);
    }

    return err;
}

int actuation_unit_step(uint8_t logic_no, struct actuation_logic *state)
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
