// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table implementation internals

#include "VGenerate_Sensor_Trips__Syms.h"
#include "VGenerate_Sensor_Trips.h"



// FUNCTIONS
VGenerate_Sensor_Trips__Syms::VGenerate_Sensor_Trips__Syms(VGenerate_Sensor_Trips* topp, const char* namep)
    // Setup locals
    : __Vm_namep(namep)
    , __Vm_didInit(false)
    // Setup submodule names
{
    // Pointer to top level
    TOPp = topp;
    // Setup each module's pointers to their submodules
    // Setup each module's pointer back to symbol table (for public functions)
    TOPp->__Vconfigure(this, true);
}
