#ifndef PLATFORM_H_
#define PLATFORM_H_
#include <stdint.h>

#include "common.h"
#include "core.h"

extern struct core_state core;

/////////////////////////////////////////
// Reading signals and values          //
/////////////////////////////////////////

/*@requires \valid(val);
  @requires div < NINSTR;
  @requires channel < NTRIP;
  @assigns *val;
  @ensures -1 <= \result <= 0;
  @ensures \result == 0 ==>  *val <= 0x80000000;
 */
int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val);

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value);
int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value);
int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value);
int get_instrumentation_maintenance(uint8_t division, uint8_t *value);

// Reading actuation signals
/*@ requires i <= 1;
  @ requires device < NDEV;
  @ requires \valid(value);
  @ assigns *value;
  @ ensures (\result == 0) ==> (*value == 0 || *value == 1);
  @ ensures (\result != 0) ==> (*value == \old(*value));
*/
int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value);

/*@requires \valid(&arr[0.. NTRIP-1][0.. NINSTR-1]);
  @assigns *(arr[0.. NTRIP-1]+(0.. NINSTR-1));
*/
int read_instrumentation_trip_signals(uint8_t arr[3][4]);

/////////////////////////////////////////
// Setting output signals              //
/////////////////////////////////////////

int reset_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t reset_val);

/*@requires logic_no < NVOTE_LOGIC;
  @requires device_no < NDEV;
  @assigns \nothing; // Not entirely true, but we'll never mention that state
  @ensures -1 <= \result <= 0;
 */
int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on);

/*@requires division < NINSTR;
  @requires channel < NTRIP;
  @assigns \nothing; // Not entirely true, but we'll never mention that state
*/
int set_output_instrumentation_trip(uint8_t division, uint8_t channel, uint8_t val);

/*@ requires device_no <= 1;
  @ assigns \nothing;
*/
int set_actuate_device(uint8_t device_no, uint8_t on);

/////////////////////////////////////////
// Sending commands between components //
/////////////////////////////////////////
int read_rts_command(struct rts_command *cmd);

/* Communicate with instrumentation division */

/*@requires division < NINSTR;
  @requires \valid(cmd);
  @assigns cmd->type, cmd->cmd;
  @ensures -1 <= \result <= 1;
*/
int read_instrumentation_command(uint8_t division, struct instrumentation_command *cmd);

/*@requires division < NINSTR;
  @requires \valid(cmd);
  @assigns \nothing; // not entirely true, but we'll never mention that state
  @ensures -1 <= \result <= 0;
*/
int send_instrumentation_command(uint8_t division, struct instrumentation_command *cmd);

/* Read external command, setting *cmd. Does not block. */
/*@requires \valid(cmd);
  @assigns cmd->on;
  @assigns cmd->device;
  @ensures -1 <= \result <= 1;
 */
int read_actuation_command(uint8_t id, struct actuation_command *cmd);

/*@requires logic < NVOTE_LOGIC;
  @requires \valid(cmd);
  @assigns \nothing; // not entirely true, but we'll never mention that state
  @ensures -1 <= \result <= 0;
*/
int send_actuation_command(uint8_t logic,
                           struct actuation_command *cmd);


/////////////////////////////////////////////
// Self Test state                         //
/////////////////////////////////////////////

/*@ assigns \nothing; */
uint8_t is_test_running(void);

/*@ assigns \nothing; */
void set_test_running(int val);

/*@ assigns \nothing;
  @ ensures \result < NDEV;
*/
uint8_t get_test_device(void);

/*@ requires \valid(id) && \valid(&id[1]);
  @ assigns id[0], id[1];
  @ ensures id[0] < NINSTR;
  @ ensures id[1] < NINSTR;
*/
void get_test_instrumentation(uint8_t *id);

/*@ assigns \nothing;
*/
int is_instrumentation_under_test(uint8_t id);

/*@ requires \valid(setpoints + (0.. NTRIP-1));
  @ requires id < NINSTR;
  @ assigns setpoints[0.. NTRIP-1];
  @ ensures -1 <= \result <= 0;
*/
int get_instrumentation_test_setpoints(uint8_t id, uint32_t *setpoints);

/*@ requires div < NINSTR;
  @ assigns core.test.test_instrumentation_done[div];
  @ ensures core.test.test_instrumentation_done[div] == v;
*/
void set_instrumentation_test_complete(uint8_t div, int v);

/*@ requires id < NINSTR;
  @ assigns \nothing;
*/
int is_instrumentation_test_complete(uint8_t id);

/*@ requires div < NINSTR;
  @ requires channel < NTRIP;
  @ requires \valid(val);
  @ assigns *val;
  @ ensures -1 <= \result <= 0;
*/
int read_test_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val);

/*@ assigns \nothing;
  @ ensures \result < NVOTE_LOGIC;
*/
uint8_t get_test_actuation_unit(void);

int is_actuation_unit_under_test(uint8_t id);
/*@ requires div < NVOTE_LOGIC;
  @ assigns core.test.test_actuation_unit_done[div];
  @ ensures core.test.test_actuation_unit_done[div] == v;
*/
void set_actuation_unit_test_complete(uint8_t div, int v);

/*@ requires id < NVOTE_LOGIC;
  @ assigns core.test.actuation_old_vote;
  @ ensures core.test.actuation_old_vote == v;
*/
void set_actuation_unit_test_input_vote(uint8_t id, int v);

/*@ requires id < NVOTE_LOGIC;
  @ assigns \nothing;
*/
int is_actuation_unit_test_complete(uint8_t id);

/*@ requires dev < NDEV;
  @ assigns core.test.test_device_result[dev];
  @ ensures core.test.test_device_result[dev] == result;
*/
void set_actuate_test_result(uint8_t dev, uint8_t result);

/*@ requires dev < NDEV;
  @ assigns core.test.test_device_done[dev];
  @ ensures core.test.test_device_done[dev] == v;
*/
void set_actuate_test_complete(uint8_t dev, int v);

/*@ requires dev < NDEV;
  @ assigns \nothing;
*/
int is_actuate_test_complete(uint8_t dev);

////////////////////////////////////////////
// General Utilities                      //
////////////////////////////////////////////
uint32_t time_in_s();

#endif // PLATFORM_H_
