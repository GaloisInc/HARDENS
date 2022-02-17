// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VGenerate_Sensor_Trips.h for the primary calling header

#include "VGenerate_Sensor_Trips.h"
#include "VGenerate_Sensor_Trips__Syms.h"

//==========

void VGenerate_Sensor_Trips::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VGenerate_Sensor_Trips::eval\n"); );
    VGenerate_Sensor_Trips__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VGenerate_Sensor_Trips* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("handwritten/SystemVerilog/instrumentation_impl.sv", 10, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VGenerate_Sensor_Trips::_eval_initial_loop(VGenerate_Sensor_Trips__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("handwritten/SystemVerilog/instrumentation_impl.sv", 10, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VGenerate_Sensor_Trips::_combo__TOP__1(VGenerate_Sensor_Trips__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VGenerate_Sensor_Trips::_combo__TOP__1\n"); );
    VGenerate_Sensor_Trips* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->out = (((vlTOPp->setpoints[2U] < vlTOPp->vals[2U]) 
                    << 2U) | (((vlTOPp->setpoints[1U] 
                                < vlTOPp->vals[1U]) 
                               << 1U) | VL_LTS_III(1,32,32, 
                                                   vlTOPp->vals[0U], 
                                                   vlTOPp->setpoints[0U])));
}

void VGenerate_Sensor_Trips::_eval(VGenerate_Sensor_Trips__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VGenerate_Sensor_Trips::_eval\n"); );
    VGenerate_Sensor_Trips* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VGenerate_Sensor_Trips::_change_request(VGenerate_Sensor_Trips__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VGenerate_Sensor_Trips::_change_request\n"); );
    VGenerate_Sensor_Trips* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VGenerate_Sensor_Trips::_change_request_1(VGenerate_Sensor_Trips__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VGenerate_Sensor_Trips::_change_request_1\n"); );
    VGenerate_Sensor_Trips* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VGenerate_Sensor_Trips::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VGenerate_Sensor_Trips::_eval_debug_assertions\n"); );
}
#endif  // VL_DEBUG
