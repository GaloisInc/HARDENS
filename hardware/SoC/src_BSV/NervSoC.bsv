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
   // TX -> a byte to be send
   method ActionValue#(Bit #(8)) get_uart_tx_byte;
   // RX -> a byte to be received
   method Action set_uart_rx_byte(Bit #(8) rx);
endinterface

// ================================================================

(* synthesize *)
module mkNervSoC (NervSoC_IFC);

   Bit#(30) memory_size = 'h40000;

   // For debugging only
   Bool show_exec_trace = False;
   Bool show_load_store = False;
   Reg #(Bit #(64)) rg_tick    <- mkReg (0);

   // Instantiate the nerv CPU
   Nerv_IFC nerv <- mkNerv;

   // Nerv has Harward architecture (separate data and instruction memory),
   // so in order to properly initialize global symbols, we need to load
   // the hex file into *both* memories.
   RegFile #(Bit #(30), Bit #(32)) imem <- mkRegFileLoad ("imem_contents.memhex32", 0, memory_size);
   RegFile #(Bit #(30), Bit #(32)) dmem <- mkRegFileLoad ("imem_contents.memhex32", 0, memory_size);

   Reg #(Bit #(32)) rg_imem_addr  <- mkReg (0);
   Reg #(Bit #(32)) rg_imem_data  <- mkRegU;
   Reg #(Bit #(32)) rg_dmem_rdata <- mkRegU;

   function Bit #(8) strb2byte (Bit #(1) b) = signExtend (b);

   // IO addresses
   Bit #(32) led_GPIO_addr = 32'h 0100_0000;
   // 7bits addr, 1bit RW
   Bit #(32) i2c_reg_addr = 32'h 0300_0000;
   // I2C fifo has up to 16 bytes (4 registers)
   // Bit #(32) i2c_reg_data_1 = 32'h 0300_0004;

   Bit #(32) uart_reg_addr_tx = 32'h 0200_0000;
   Bit #(32) uart_reg_addr_rx = 32'h 0200_0004;
   Bit #(32) uart_reg_addr_data_ready = 32'h 0200_0008;

   // IO registers
   Reg #(Bit #(32)) rg_leds       <- mkRegU;
   Reg #(Bit #(8)) rg_uart_tx <- mkReg(0);
   Reg #(Bit #(8)) rg_uart_rx <- mkReg(0);
   Reg #(Bool) rg_uart_rx_data_ready <- mkReg(False);
   Reg #(Bool) rg_uart_tx_data_ready <- mkReg(False);

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

      case (d_addr)
         // Write to GPIO LED pins
         // TODO: repurpose for generic actuator IO
         led_GPIO_addr:
            begin
               rg_leds <= ((rg_leds & (~ mask)) | (wdata & mask));
            end
         // Write a byte to serial port
         uart_reg_addr_tx:
            begin
               rg_uart_tx <= wdata[7:0];
               rg_uart_tx_data_ready <= True;
            end
         // Receive data from serial port
         // Note: might be 0 or stale, check uart_reg_addr_data_ready first
         uart_reg_addr_rx:
            begin
               rg_dmem_rdata <= signExtend(rg_uart_rx);
               rg_uart_rx_data_ready <= False;
            end
         uart_reg_addr_data_ready:
            begin
               if (rg_uart_rx_data_ready)
                  rg_dmem_rdata <= 1;
               else
               rg_dmem_rdata <= 0;
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
   // TX -> a byte to be send
   method ActionValue#(Bit #(8)) get_uart_tx_byte () if (rg_uart_tx_data_ready);
      begin
         rg_uart_tx_data_ready <= False;
         return rg_uart_tx;
      end
   endmethod
   // Rx -> a byte to be received
   method Action set_uart_rx_byte(Bit #(8) rx);
      begin
         rg_uart_rx_data_ready <= True;
         rg_uart_rx <= rx;
      end
   endmethod

endmodule

// ================================================================

endpackage
