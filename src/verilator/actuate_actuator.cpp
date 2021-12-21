#include "actuate_actuator/VActuateActuator.h"
#include <stdint.h>

VActuateActuator actuate;

extern "C" uint8_t ActuateActuator(uint8_t inp)
{
    actuate.inputs = inp;
    actuate.eval();
    return actuate.out;
}
