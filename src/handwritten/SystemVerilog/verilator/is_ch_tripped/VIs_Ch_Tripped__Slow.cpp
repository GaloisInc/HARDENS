// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VIs_Ch_Tripped.h for the primary calling header

#include "VIs_Ch_Tripped.h"
#include "VIs_Ch_Tripped__Syms.h"

//==========

VL_CTOR_IMP(VIs_Ch_Tripped) {
    VIs_Ch_Tripped__Syms* __restrict vlSymsp = __VlSymsp = new VIs_Ch_Tripped__Syms(this, name());
    VIs_Ch_Tripped* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VIs_Ch_Tripped::__Vconfigure(VIs_Ch_Tripped__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VIs_Ch_Tripped::~VIs_Ch_Tripped() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VIs_Ch_Tripped::_eval_initial(VIs_Ch_Tripped__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VIs_Ch_Tripped::_eval_initial\n"); );
    VIs_Ch_Tripped* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VIs_Ch_Tripped::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VIs_Ch_Tripped::final\n"); );
    // Variables
    VIs_Ch_Tripped__Syms* __restrict vlSymsp = this->__VlSymsp;
    VIs_Ch_Tripped* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VIs_Ch_Tripped::_eval_settle(VIs_Ch_Tripped__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VIs_Ch_Tripped::_eval_settle\n"); );
    VIs_Ch_Tripped* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VIs_Ch_Tripped::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VIs_Ch_Tripped::_ctor_var_reset\n"); );
    // Body
    mode = VL_RAND_RESET_I(2);
    sensor_tripped = VL_RAND_RESET_I(1);
    out = VL_RAND_RESET_I(1);
}
