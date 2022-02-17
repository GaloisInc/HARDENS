// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VGENERATE_SENSOR_TRIPS__SYMS_H_
#define _VGENERATE_SENSOR_TRIPS__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VGenerate_Sensor_Trips.h"

// SYMS CLASS
class VGenerate_Sensor_Trips__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VGenerate_Sensor_Trips*        TOPp;
    
    // CREATORS
    VGenerate_Sensor_Trips__Syms(VGenerate_Sensor_Trips* topp, const char* namep);
    ~VGenerate_Sensor_Trips__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
