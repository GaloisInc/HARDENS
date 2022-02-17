// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VGenerate_Sensor_Trips.h for the primary calling header

#include "VGenerate_Sensor_Trips.h"
#include "VGenerate_Sensor_Trips__Syms.h"

//==========

VL_CTOR_IMP(VGenerate_Sensor_Trips) {
    VGenerate_Sensor_Trips__Syms* __restrict vlSymsp = __VlSymsp = new VGenerate_Sensor_Trips__Syms(this, name());
    VGenerate_Sensor_Trips* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VGenerate_Sensor_Trips::__Vconfigure(VGenerate_Sensor_Trips__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VGenerate_Sensor_Trips::~VGenerate_Sensor_Trips() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VGenerate_Sensor_Trips::_eval_initial(VGenerate_Sensor_Trips__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VGenerate_Sensor_Trips::_eval_initial\n"); );
    VGenerate_Sensor_Trips* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VGenerate_Sensor_Trips::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VGenerate_Sensor_Trips::final\n"); );
    // Variables
    VGenerate_Sensor_Trips__Syms* __restrict vlSymsp = this->__VlSymsp;
    VGenerate_Sensor_Trips* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VGenerate_Sensor_Trips::_eval_settle(VGenerate_Sensor_Trips__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VGenerate_Sensor_Trips::_eval_settle\n"); );
    VGenerate_Sensor_Trips* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VGenerate_Sensor_Trips::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VGenerate_Sensor_Trips::_ctor_var_reset\n"); );
    // Body
    VL_RAND_RESET_W(96, vals);
    VL_RAND_RESET_W(96, setpoints);
    out = VL_RAND_RESET_I(3);
}
