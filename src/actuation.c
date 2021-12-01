#include "actuation.h"

/* Read trip signals
 * @requires arr is NTRIP elements
 * @ensures arr[0..3] set to the current trip input signals
 * @ensures \ret < 0 on error
 */
extern int
read_trip_signals(uint8_t *arr);

/* Read external command, setting *cmd. Does not block.
 * @requires cmd valid
 * @ensures \ret < 0 on error, \ret == 0 if no command,
 *   \ret > 0 if the cmd structure was filled in with a waiting
 *   command
 */
extern int
read_actuation_command(struct manual_actuation_command *cmd);

/* (De)Activate an actuator
 * @ensures \ret < 0 on error
 */
extern int
actuate_device(uint8_t device_no, uint8_t on);

int
actuation_logic_step(struct actuation_logic *state)
{
    int err = 0;
    uint8_t trip[4];

    err = read_trip_signals(trip);
    if(err) return err;

    uint8_t votes = Voting_Step(trip);

    for (int i = 0; i < NDEV; ++i) {
        state->vote_actuate[i] = VOTE_I(votes, i);
    }

    return err;
}

int
actuation_handle_command(struct actuation_logic *state)
{
    int read_command = 0;
    struct manual_actuation_command cmd;

    read_command = read_actuation_command(&cmd);
    if (read_command < 0) return read_command;

    if (read_command) {
        state->manual_actuate[cmd.device] = cmd.on;
    }

    return 0;
}

int
actuate_devices(struct actuation_logic *state)
{
    int err = 0;
    for (int d = 0; d < NDEV; ++d) {
        uint8_t on = state->vote_actuate[d] || state->manual_actuate[d];
        // @abakst if it's a problem to actuate "on"
        // repeatedly then we just need to track this state in the
        // actuation logic struct.
        err |= actuate_device(d, on);
    }

    return err;
}

int
actuation_step(struct actuation_logic *state)
{
    int err = 0;
    /* Read trip signals & vote */
    err = actuation_logic_step(state);
    if(err) return err;

    /* Handle any external commands */
    err = actuation_handle_command(state);
    if(err) return err;

    /* Actuate devices based on voting and commands */
    err = actuate_devices(state);
    return err;
}
