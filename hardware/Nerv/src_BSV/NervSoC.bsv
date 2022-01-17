// Copyright (c) 2022 Rishiyur S. Nikhil

package NervSoC;

// ================================================================
// Module mkNervSoC is a BSV version of nervsoc.sv

// nervsoc.sv is from:    https://github.com/YosysHQ/nerv

// ================================================================
// Import from BSV library

import RegFile :: *;

// ================================================================
// Local imports

import Nerv :: *;

// ================================================================
// A small NERV SoC

interface NervSoC_IFC;
   method Bit #(32) leds;
endinterface

// ================================================================

(* synthesize *)
module mkNervSoC (NervSoC_IFC);

   // For debugging only
   Bool show_exec_trace = False;
   Bool show_load_store = False;
   Reg #(Bit #(64)) rg_tick <- mkReg (0);

   // Instantiate the nerv CPU
   Nerv_IFC nerv <- mkNerv;

   RegFile #(Bit #(30), Bit #(32)) imem <- mkRegFileLoad ("imem_contents.memhex32", 0, 1023);
   RegFile #(Bit #(30), Bit #(32)) dmem <- mkRegFile (0, 1023);

   Reg #(Bit #(32)) rg_leds       <- mkRegU;
   Reg #(Bit #(32)) rg_imem_addr  <- mkReg (0);
   Reg #(Bit #(32)) rg_imem_data  <- mkRegU;
   Reg #(Bit #(32)) rg_dmem_rdata <- mkRegU;

   function Bit #(8) strb2byte (Bit #(1) b) = signExtend (b);

   // This rule deals with instruction fetch and D-Mem read results
   (* fire_when_enabled, no_implicit_conditions *)
   rule rl_always;
      let i_addr = nerv.m_imem_addr;
      rg_imem_addr <= i_addr;
      rg_imem_data <= imem.sub (i_addr [31:2]);

      nerv.m_stall (False);
      nerv.m_imem_data (rg_imem_data);
      nerv.m_dmem_rdata (rg_dmem_rdata);

      if (show_exec_trace)
	 $display ("%0d: PC 0x%0h  Instr 0x%0h  Next PC 0x%0h",
		   rg_tick, rg_imem_addr, rg_imem_data, i_addr);

      // Note: not using trap for anything
      let trap = nerv.m_trap;
      if (trap) $display ("Trapped");

      rg_tick <= rg_tick + 1;
   endrule

   // This rule deals with D-Mem writes and LED GPIO writes
   rule rl_memop;
      let d_addr     = nerv.m_dmem_addr;
      let mem_data = dmem.sub (d_addr [31:2]);
      let dmw      = nerv.m_get_dmem;
      let wstrb    = dmw.wstrb;
      let wdata    = dmw.wdata;
      if (show_load_store)
	 $display ("DMem addr 0x%0h  wstrb 0x%0h  wdata 0x%0h" , d_addr, wstrb, wdata);

      let mask  = {strb2byte (wstrb [3]),
		   strb2byte (wstrb [2]),
		   strb2byte (wstrb [1]),
		   strb2byte (wstrb [3])};

      Bit #(32) led_GPIO_addr = 32'h 0100_0000;
      if (d_addr == led_GPIO_addr)
	 rg_leds <= ((rg_leds & (~ mask)) | (wdata & mask));
      else
	 dmem.upd (d_addr [31:2], ((mem_data & (~ mask)) | (wdata & mask)));

      rg_dmem_rdata <= mem_data;
   endrule

   // ================================================================
   // INTERFACE

   method Bit #(32) leds = rg_leds;

endmodule

// ================================================================

endpackage
