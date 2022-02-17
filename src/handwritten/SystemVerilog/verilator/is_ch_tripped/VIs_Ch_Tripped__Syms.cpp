// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table implementation internals

#include "VIs_Ch_Tripped__Syms.h"
#include "VIs_Ch_Tripped.h"



// FUNCTIONS
VIs_Ch_Tripped__Syms::VIs_Ch_Tripped__Syms(VIs_Ch_Tripped* topp, const char* namep)
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
