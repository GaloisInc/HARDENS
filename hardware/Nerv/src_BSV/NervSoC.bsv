package NervSoC;

import RegFile :: *;

import Nerv :: *;

// ================================================================
// A small NERV SoC

interface NervSoC_IFC;
   method Bit #(32) leds;
endinterface

// ================================================================

(* synthesize *)
module mkNervSoC (NervSoC_IFC);

   Nerv_IFC nerv <- mkNerv;

   RegFile #(Bit #(30), Bit #(32)) imem <- mkRegFileLoad ("firmware.hex",0,1023);
   RegFile #(Bit #(30), Bit #(32)) dmem <- mkRegFile(0,1023);

   Reg #(Bit #(32)) rg_leds <- mkRegU;
   Reg #(Bit #(32)) rg_dmem_rdata <- mkRegU;

   function Bit #(8) strb2byte (Bit #(1) b) = signExtend (b);

   (* fire_when_enabled, no_implicit_conditions *)
   rule rl_always;
      let addr = nerv.m_imem_addr [31:2];
      nerv.m_imem_data (imem.sub (addr));
      //nerv.m_imem_data (0);
      nerv.m_stall (False);
      nerv.m_dmem_rdata (rg_dmem_rdata);
      //nerv.m_dmem_rdata (0);

      // Note: not using trap for anything
      let trap = nerv.m_trap;
   endrule

   rule rl_memop;
      let addr     = nerv.m_dmem_addr;
      let mem_data = dmem.sub (addr [31:2]);
      let dmw      = nerv.m_get_dmem;
      let wstrb    = dmw.wstrb;
      let wdata    = dmw.wdata;

      let mask  = {strb2byte (wstrb [3]),
		   strb2byte (wstrb [2]),
		   strb2byte (wstrb [1]),
		   strb2byte (wstrb [3])};

      if (addr == 32'h 0100_0000)
	      rg_leds <= ((rg_leds & (~ mask)) | (wdata & mask));
      else
	      dmem.upd (addr [31:2], ((mem_data & (~ mask)) | (wdata & mask)));

      rg_dmem_rdata <= mem_data;
   endrule

   // ================================================================
   // INTERFACE

   method Bit #(32) leds = rg_leds;

endmodule

// ================================================================

endpackage
