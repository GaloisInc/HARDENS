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

/////////////////////////////////////////
// Setting output signals              //
/////////////////////////////////////////

/* Output decision from an actuation logic
 * @ensures \ret < 0 on error
 */
int reset_actuation_logic(uint8_t logic_no, uint8_t device_no, uint8_t reset_val);
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
