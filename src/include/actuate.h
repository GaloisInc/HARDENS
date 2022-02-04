#ifndef ACTUATE_H_
#define ACTUATE_H_

#include <stdint.h>
#include "models.acsl"

// Combine the votes from both actuate logic components
// and tell the hardware device to actuate (or unactuate)
int actuate_devices(void);

// Return whether or not a device with the provided votes should be actuated
// Bit i = vote by logic unit i
// This function is generated directly from the Cryptol model
/*@ assigns \nothing;
  @ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 <==> ((vs & 0x01) || (vs & 0x02));
  @ ensures ActuateActuator(vs) <==> \result == 1;
*/
uint8_t ActuateActuator(uint8_t vs);

#endif // ACTUATE_H_
