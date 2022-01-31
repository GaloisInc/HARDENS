#ifndef PLATFORM_H_
#define PLATFORM_H_
#include <stdint.h>

#include "common.h"

/////////////////////////////////////////
// Reading signals and values          //
/////////////////////////////////////////

/*@requires \valid(val);
  @requires div <= 3;
  @requires channel <= 2;
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
  @ requires device <= 1;
  @ requires \valid(value);
  @ assigns *value;
  @ ensures (\result == 0) ==> (*value == 0 || *value == 1);
  @ ensures (\result != 0) ==> (*value == \old(*value));
*/
int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value);

/*@requires \valid(arr);
  @assigns *(arr[0..2]+(0..3));
*/
int read_instrumentation_trip_signals(uint8_t arr[3][4]);

/////////////////////////////////////////
// Setting output signals              //
/////////////////////////////////////////

/*@requires logic_no <= 1;
  @requires device_no <= 1;
  @requires on == 0 || on == 1;
  @assigns \nothing; // Not entirely true, but we'll never mention that state
  @ensures -1 <= \result <= 0;
 */
int reset_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t reset_val);
int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on);

/*@requires division <= 3;
  @requires channel <= 2;
  @requires val <= 1;
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

/*@requires division <= 3;
  @requires \valid(cmd);
  @assigns cmd->type, cmd->cmd;
  @ensures -1 <= \result <= 1;
*/
int read_instrumentation_command(uint8_t division, struct instrumentation_command *cmd);
int send_instrumentation_command(uint8_t division, struct instrumentation_command *cmd);

/* Read external command, setting *cmd. Does not block. */
/*@requires \valid(cmd);
  @assigns cmd->on;
  @assigns cmd->device;
  @ensures -1 <= \result <= 1;
 */
int read_actuation_command(uint8_t id, struct actuation_command *cmd);

int send_actuation_command(uint8_t actuator,
                           struct actuation_command *cmd);


int set_display_line(uint8_t line_number, const char *display, uint32_t size);


/////////////////////////////////////////////
// Self Test state                         //
/////////////////////////////////////////////
uint8_t is_test_running();
void set_test_running(int val);
uint8_t get_test_device();

void get_test_instrumentation(uint8_t *id);
int is_instrumentation_under_test(uint8_t id);
int get_instrumentation_test_setpoints(uint8_t id, uint32_t *setpoints);
void set_instrumentation_test_complete(uint8_t div, int v);
int is_instrumentation_test_complete(uint8_t id);
int read_test_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val);

uint8_t get_test_actuation_unit();
int is_actuation_unit_under_test(uint8_t id);
void set_actuation_unit_test_complete(uint8_t div, int v);
void set_actuation_unit_test_input_vote(uint8_t id, int v);
int is_actuation_unit_test_complete(uint8_t id);

void set_actuate_test_result(uint8_t dev, uint8_t result);
void set_actuate_test_complete(uint8_t dev, int v);
int is_actuate_test_complete(uint8_t dev);

////////////////////////////////////////////
// General Utilities                      //
////////////////////////////////////////////
uint32_t time_in_s();

#endif // PLATFORM_H_
