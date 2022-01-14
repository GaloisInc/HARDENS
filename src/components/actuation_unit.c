#include "actuation_logic.h"
#include "common.h"
#include "platform.h"


#define VOTE_I(_v, _i) (((_v) >> (_i)) & 0x1)

static int
actuation_logic_vote(uint8_t logic_no, int do_test, struct actuation_logic *state)
{
    int err = 0;
    uint8_t trip[3][4];
    uint8_t trip_test[3][4];
    uint8_t test_div[2];

    get_test_instrumentation(test_div);

    int valid[4];
    for (int i = 0; i < NINSTR; ++i) {
        valid[i] = get_instrumentation_output_valid(i);
    }

    err |= read_instrumentation_trip_signals(trip);

    for (int i = 0; i < NINSTR; ++i) {
        uint8_t test_signal = (i == test_div[0] || i == test_div[1]);
        for (int c = 0; c < NTRIP; ++c) {
            if (do_test) {
                trip_test[c][i] = trip[c][i] & test_signal;
                trip[c][i] &= !test_signal;
            } else {
                trip[c][i] &= valid[i];
            }
        }
    }

    if (do_test && get_test_device() == 0) {
        if (!is_actuation_unit_test_complete(logic_no)) {
            state->vote_actuate[0] = Actuate_D0(trip_test, state->vote_actuate[0] != 0);
        }
    } else {
        state->vote_actuate[0] = Actuate_D0(trip, state->vote_actuate[0] != 0);
    }

    if (do_test && get_test_device() == 1) {
        if (!is_actuation_unit_test_complete(logic_no)) {
            state->vote_actuate[1] = Actuate_D1(trip_test, state->vote_actuate[1] != 0);
        }
    } else {
        state->vote_actuate[1] = Actuate_D1(trip, state->vote_actuate[1] != 0);
    }

    return err;
}

static int
actuation_handle_command(uint8_t logic_no, struct actuation_command *cmd, struct actuation_logic *state)
{
    state->manual_actuate[cmd->device] = cmd->on;
    return 0;
}

static int
output_actuation_signals(uint8_t logic_no, int do_test, struct actuation_logic *state)
{
    int err = 0;
    if (do_test) {
        set_actuation_unit_output_valid(logic_no, 0);
    }
    for (int d = 0; d < NDEV; ++d) {
        uint8_t on = state->vote_actuate[d] || state->manual_actuate[d];
        if (!do_test || !is_actuation_unit_test_complete(logic_no)) {
            err |= set_output_actuation_logic(logic_no, d, on);
        }
    }
    if (do_test && !is_actuation_unit_test_complete(logic_no)) {
        // Reset internal state
        state->vote_actuate[0] = 0;
        state->vote_actuate[1] = 0;
        uint8_t this_vote;
        get_actuation_state(logic_no, 0, &this_vote);
        set_actuation_unit_test_complete(logic_no, 1);
    }

    return err;
}

int actuation_unit_step(uint8_t logic_no, struct actuation_logic *state)
{
    int err = 0;
    uint8_t test_div[2];

    get_test_instrumentation(test_div);
    int do_test = logic_no == get_test_actuation_unit() &&
                  is_instrumentation_test_complete(test_div[0]) &&
                  is_instrumentation_test_complete(test_div[1]) &&
                  is_test_running();

    if (do_test && is_actuation_unit_test_complete(logic_no))
        return 0;

    if (!do_test && is_actuation_unit_test_complete(logic_no)) {
        set_output_actuation_logic(logic_no, get_test_device(), 0);
        set_actuation_unit_output_valid(logic_no, 1);
        set_actuation_unit_test_complete(logic_no, 0);
        return 0;
    }

    /* Read trip signals & vote */
    err |= actuation_logic_vote(logic_no, do_test, state);

    /* Handle any external commands */
    struct actuation_command cmd;
    int read_cmd = read_actuation_command(logic_no, &cmd);
    if (read_cmd > 0) {
        err |= actuation_handle_command(logic_no, &cmd, state);
    } else if (read_cmd < 0) {
        err |= -read_cmd;
    }

    /* Actuate devices based on voting and commands */
    err |= output_actuation_signals(logic_no, do_test, state);
    return err;
}
