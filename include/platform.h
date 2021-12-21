#ifndef PLATFORM_H_
#define PLATFORM_H_
#include <stdint.h>

#include "common.h"

/////////////////////////////////////////
// Reading signals and values          //
/////////////////////////////////////////

/* Read the value of channel `channel`, setting *val on success;
 * @return < 0 on error
 */
int read_instrumentation_channel(uint8_t div, uint8_t channel, uint32_t *val);

int get_instrumentation_value(uint8_t division, uint8_t ch, uint32_t *value);
int get_instrumentation_trip(uint8_t division, uint8_t ch, uint8_t *value);
int get_instrumentation_mode(uint8_t division, uint8_t ch, uint8_t *value);
int get_instrumentation_maintenance(uint8_t division, uint8_t *value);

// Reading actuation signals
int get_actuation_state(uint8_t i, uint8_t device, uint8_t *value);

/* Read trip signals
 * @requires arr is NTRIP elements
 * @ensures arr[0..3] set to the current trip input signals
 * @ensures \ret < 0 on error
 */
int read_instrumentation_trip_signals(uint8_t arr[3][4]);

// @todo move me
uint32_t saturation(uint32_t temp, uint32_t pressure);

/////////////////////////////////////////
// Setting output signals              //
/////////////////////////////////////////

/* Output decision from an actuation logic
 * @ensures \ret < 0 on error
 */
int set_output_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t on);
int set_output_instrumentation_trip(uint8_t division, uint8_t channel, uint8_t val);
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