#ifndef PLATFORM_H_
#define PLATFORM_H_
#include <stdint.h>

#include "common.h"

/////////////////////////////////////////
// Reading signals and values          //
/////////////////////////////////////////

/* @requires \valid(val);
   @requires div <= 3;
   @requires channel <= 2;
   @assigns *val;
behavior ok:
   @ensures \result == 0;
   @ensures *val <= 0x80000000;
behavior err:
   @ensures \result < 0;
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
behavior ok:
  @ensures \result == 0;
  @ensures *value == 0 || *value == 1;
behavior error:
  @ensures \result != 0;
  @ensures *value == \old(*value);
*/
int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value);

/*@requires \valid(arr);
  @assigns *(arr[0..2]+(0..3));
*/
int read_instrumentation_trip_signals(uint8_t arr[3][4]);

/////////////////////////////////////////
// Setting output signals              //
/////////////////////////////////////////

/* Output decision from an actuation logic
 * @ensures \ret < 0 on error
 */
int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on);
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
int read_instrumentation_command(uint8_t division, struct instrumentation_command *cmd);
int send_instrumentation_command(uint8_t division, struct instrumentation_command *cmd);

/* Read external command, setting *cmd. Does not block.
 * @requires cmd valid
 * @ensures \ret < 0 on error, \ret == 0 if no command,
 *   \ret > 0 if the cmd structure was filled in with a waiting
 *   command
 */
int read_actuation_command(uint8_t id, struct actuation_command *cmd);

int send_actuation_command(uint8_t actuator,
                           struct actuation_command *cmd);


int set_display_line(uint8_t line_number, char *display, uint32_t size);

#endif // PLATFORM_H_
