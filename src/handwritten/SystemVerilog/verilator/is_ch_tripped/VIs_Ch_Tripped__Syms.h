// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VIS_CH_TRIPPED__SYMS_H_
#define _VIS_CH_TRIPPED__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VIs_Ch_Tripped.h"

// SYMS CLASS
class VIs_Ch_Tripped__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VIs_Ch_Tripped*                TOPp;
    
    // CREATORS
    VIs_Ch_Tripped__Syms(VIs_Ch_Tripped* topp, const char* namep);
    ~VIs_Ch_Tripped__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
