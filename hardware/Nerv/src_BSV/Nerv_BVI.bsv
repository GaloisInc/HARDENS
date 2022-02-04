// Copyright (c) 2022 Rishiyur S. Nikhil

package Nerv_BVI;

// ================================================================
// Module mkNerv_BVI imports the SystemVerilog module nerv.sv so that
// it can be used in BSV.
// nerv.sv is from:    https://github.com/YosysHQ/nerv

// ================================================================
// Import from BSV library

import Clocks :: *;

// ================================================================
// BSV "raw" interface for nerv.sv (nerv CPU)

interface Nerv_BVI_IFC;
   (* always_ready, always_enabled *)
   method Action m_stall (Bool b);
   (* always_ready *)
   method Bool m_trap;

   (* always_ready *)
   method Bit #(32) m_imem_addr;
   (* always_ready, always_enabled *)
   method Action m_imem_data (Bit #(32) xi);

   (* always_ready *)
   method Bool  m_dmem_valid;
   (* always_ready *)
   method Bit #(32) m_dmem_addr;
   (* always_ready *)
   method Bit #(4)  m_dmem_wstrb;
   (* always_ready *)
   method Bit #(32) m_dmem_wdata;
   (* always_ready, always_enabled *)
   method Action m_dmem_rdata (Bit #(32) xd);
endinterface

// ================================================================

import "BVI" nerv =
module mkNerv_BVI (Nerv_BVI_IFC);
   default_clock (clock);

   // BSV's default reset (including this module's reset) is active low
   // The imported nerv.sv's reset is active high.
   default_reset (reset) <- invertCurrentReset;

   method m_stall (stall) enable ((*inhigh*) EN0);    // BSV -> Verilog
   method trap m_trap;                  // BSV <- Verilog

   method imem_addr m_imem_addr;        // BSV <- Verilog
   method m_imem_data (imem_data) enable ((*inhigh*) EN1);    // BSV -> Verilog

   method dmem_valid   m_dmem_valid;    // BSV <- Verilog
   method dmem_addr    m_dmem_addr;     // BSV <- Verilog
   method dmem_wstrb   m_dmem_wstrb;    // BSV <- Verilog
   method dmem_wdata   m_dmem_wdata;    // BSV <- Verilog
   method m_dmem_rdata (dmem_rdata) enable ((*inhigh*) EN2);    // BSV -> Verilog

   // Declaring each method conflict-free with each method.
   // This is ok if everything is registered, but dicey if there are
   // combinational paths weaving in and out of the module.
      schedule
      (m_stall,
       m_trap,
       m_imem_addr,
       m_imem_data,
       m_dmem_valid,
       m_dmem_addr,
       m_dmem_wstrb,
       m_dmem_wdata,
       m_dmem_rdata)  CF  (m_stall,
			   m_trap,
			   m_imem_addr,
			   m_imem_data,
			   m_dmem_valid,
			   m_dmem_addr,
			   m_dmem_wstrb,
			   m_dmem_wdata,
			   m_dmem_rdata);
endmodule

// ================================================================

endpackage
