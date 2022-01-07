#ifndef ACTUATE_H_
#define ACTUATE_H_

// Combine the votes from both actuate logic components
// and tell the hardware device to actuate (or unactuate)
#include <stdint.h>
int actuate_devices(void);

// Return whether or not a device with the provided votes should be actuated
// Bit i = vote by logic unit i
// This function is generated directly from the Cryptol model
uint8_t ActuateActuator(uint8_t vs);

#endif // ACTUATE_H_
