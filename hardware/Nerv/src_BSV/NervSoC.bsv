// Copyright (c) 2022 Rishiyur S. Nikhil

package NervSoC;

// ================================================================
// Module mkNervSoC is a BSV version of nervsoc.sv

// nervsoc.sv is from:    https://github.com/YosysHQ/nerv

// ================================================================
// Import from BSV library

import RegFile :: *;
import I2C :: *;
import RS232 :: *;
import GetPut::*;
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
   //0x001000
   Bit#(30) memory_size = 'h40000;

   // For debugging only
   Bool show_exec_trace = False;
   Bool show_load_store = False;
   Reg #(Bit #(64)) rg_tick <- mkReg (0);
   Reg #(Bit #(32)) rg_uart       <- mkRegU;
   Reg #(Bit #(32)) rg_i2c       <- mkRegU;

   // I/O peripherals
   // @podhrmic TODO: check the prescalers
   I2C i2c <- mkI2C(16);
   UART #(4) uart <- mkUART(8, NONE, STOP_1, 16);

   // Instantiate the nerv CPU
   Nerv_IFC nerv <- mkNerv;

   // Nerv has Harward architecture (separate data and instruction memory),
   // so in order to properly initialize global symbols, we need to load
   // the hex file into *both* memories
   RegFile #(Bit #(30), Bit #(32)) imem <- mkRegFileLoad ("imem_contents.memhex32", 0, memory_size);
   RegFile #(Bit #(30), Bit #(32)) dmem <- mkRegFileLoad ("imem_contents.memhex32", 0, memory_size);

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

      let mask  = {strb2byte (wstrb [3]),
           strb2byte (wstrb [2]),
           strb2byte (wstrb [1]),
           strb2byte (wstrb [0])};
      
      if (show_load_store)
         $display ("DMem addr 0x%0h  wstrb 0x%0h  wdata 0x%0h mask 0x%0h" , d_addr, wstrb, wdata, mask);

      Bit #(32) led_GPIO_addr = 32'h 0100_0000;
      Bit #(32) i2c_reg_addr = 32'h 0300_0000;

      Bit #(32) uart_reg_addr_tx = 32'h 0200_0000;
      Bit #(32) uart_reg_addr_rx = 32'h 0200_0004;

      case (d_addr)
         led_GPIO_addr:
            begin
               rg_leds <= ((rg_leds & (~ mask)) | (wdata & mask));
            end
         uart_reg_addr_tx:
            begin
               let newval = ((rg_uart & (~ mask)) | (wdata & mask));
               rg_uart <= newval;
               // Accept only first 8 bits
               $display("Writing to uart: 0x%0h, %c",newval, newval);
               uart.rx.put(newval[8:1]);
            end
         uart_reg_addr_rx:
            begin
               // We requested a read from the UART FIFO
               // Return the first value from FIFO
               // @podhrmic: What to do if the fifo is empty?
               let val <- uart.tx.get();
               $display("Reading from uart 0x%0h", val);
               let extended_val = signExtend(val);
               rg_dmem_rdata <= extended_val;
            end
         i2c_reg_addr:
            begin
               $display("Unimplemented");
            end
         default:
            begin
               // Regular memory read
               dmem.upd (d_addr [31:2], ((mem_data & (~ mask)) | (wdata & mask)));
               rg_dmem_rdata <= mem_data;
            end
      endcase
   endrule

   rule trap;
      if (nerv.m_trap)
         $finish(0);
   endrule

   // ================================================================
   // INTERFACE

   method Bit #(32) leds = rg_leds;

endmodule

// ================================================================

endpackage
