#include "stdint.h"

#define _ExtInt_1 char
#define _ExtInt_2 char
#define _ExtInt_3 char
#define _ExtInt_4 char
#define _ExtInt_32 int
#define _ExtInt(w) _ExtInt_##w

#include "step_trip_signals.inc.c"
