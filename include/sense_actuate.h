#ifndef SENSE_ACTUATE_H_
#define SENSE_ACTUATE_H_

#include "common.h"
#include "instrumentation.h"
#include "actuation_logic.h"

/* Initialize state for core `core_id`.
 * @requires instrumentation is an array of NINSTRUMENTATION/NCORE_ID instrumentation structs
 * @requires actuation_logic is an array of NACTUATION_LOGIC/NCORE_ID actuation_logic structs
 * @returns < 0 on error
 */
int sense_actuate_init(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation);

/* Advance state for core `core_id`.
 * @requires instrumentation is an array of NINSTRUMENTATION/NCORE_ID instrumentation structs
 * @requires actuation_logic is an array of NACTUATION_LOGIC/NCORE_ID actuation_logic structs
 * @returns < 0 on error
 */
int sense_actuate_step(int core_id,
                       struct instrumentation_state *instrumentation,
                       struct actuation_logic *actuation);

#endif // SENSE_ACTUATE_H_
