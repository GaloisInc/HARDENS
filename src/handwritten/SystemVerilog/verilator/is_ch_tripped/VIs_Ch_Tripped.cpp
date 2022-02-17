// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VIs_Ch_Tripped.h for the primary calling header

#include "VIs_Ch_Tripped.h"
#include "VIs_Ch_Tripped__Syms.h"

//==========

void VIs_Ch_Tripped::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VIs_Ch_Tripped::eval\n"); );
    VIs_Ch_Tripped__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VIs_Ch_Tripped* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
#ifdef VL_DEBUG
    // Debug assertions
    _eval_debug_assertions();
#endif  // VL_DEBUG
    // Initialize
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) _eval_initial_loop(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Clock loop\n"););
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("handwritten/SystemVerilog/instrumentation_impl.sv", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VIs_Ch_Tripped::_eval_initial_loop(VIs_Ch_Tripped__Syms* __restrict vlSymsp) {
    vlSymsp->__Vm_didInit = true;
    _eval_initial(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        _eval_settle(vlSymsp);
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("handwritten/SystemVerilog/instrumentation_impl.sv", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VIs_Ch_Tripped::_combo__TOP__1(VIs_Ch_Tripped__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VIs_Ch_Tripped::_combo__TOP__1\n"); );
    VIs_Ch_Tripped* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->out = ((2U == (IData)(vlTOPp->mode)) | 
                   ((1U == (IData)(vlTOPp->mode)) & (IData)(vlTOPp->sensor_tripped)));
}

void VIs_Ch_Tripped::_eval(VIs_Ch_Tripped__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VIs_Ch_Tripped::_eval\n"); );
    VIs_Ch_Tripped* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VIs_Ch_Tripped::_change_request(VIs_Ch_Tripped__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VIs_Ch_Tripped::_change_request\n"); );
    VIs_Ch_Tripped* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VIs_Ch_Tripped::_change_request_1(VIs_Ch_Tripped__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VIs_Ch_Tripped::_change_request_1\n"); );
    VIs_Ch_Tripped* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VIs_Ch_Tripped::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VIs_Ch_Tripped::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((mode & 0xfcU))) {
        Verilated::overWidthError("mode");}
    if (VL_UNLIKELY((sensor_tripped & 0xfeU))) {
        Verilated::overWidthError("sensor_tripped");}
}
#endif  // VL_DEBUG
