// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef _VIS_CH_TRIPPED_H_
#define _VIS_CH_TRIPPED_H_  // guard

#include "verilated.h"

//==========

class VIs_Ch_Tripped__Syms;

//----------

VL_MODULE(VIs_Ch_Tripped) {
  public:
    
    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(mode,1,0);
    VL_IN8(sensor_tripped,0,0);
    VL_OUT8(out,0,0);
    
    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    VIs_Ch_Tripped__Syms* __VlSymsp;  // Symbol table
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(VIs_Ch_Tripped);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// The special name  may be used to make a wrapper with a
    /// single model invisible with respect to DPI scope names.
    VIs_Ch_Tripped(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    ~VIs_Ch_Tripped();
    
    // API METHODS
    /// Evaluate the model.  Application must call when inputs change.
    void eval() { eval_step(); }
    /// Evaluate when calling multiple units/models per time step.
    void eval_step();
    /// Evaluate at end of a timestep for tracing, when using eval_step().
    /// Application must call after all eval() and before time changes.
    void eval_end_step() {}
    /// Simulation complete, run final blocks.  Application must call on completion.
    void final();
    
    // INTERNAL METHODS
  private:
    static void _eval_initial_loop(VIs_Ch_Tripped__Syms* __restrict vlSymsp);
  public:
    void __Vconfigure(VIs_Ch_Tripped__Syms* symsp, bool first);
  private:
    static QData _change_request(VIs_Ch_Tripped__Syms* __restrict vlSymsp);
    static QData _change_request_1(VIs_Ch_Tripped__Syms* __restrict vlSymsp);
  public:
    static void _combo__TOP__1(VIs_Ch_Tripped__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset() VL_ATTR_COLD;
  public:
    static void _eval(VIs_Ch_Tripped__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(VIs_Ch_Tripped__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(VIs_Ch_Tripped__Syms* __restrict vlSymsp) VL_ATTR_COLD;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
