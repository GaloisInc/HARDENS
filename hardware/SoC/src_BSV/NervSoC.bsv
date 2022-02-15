// Copyright (c) 2022 Rishiyur S. Nikhil

package NervSoC;

// ================================================================
// Module mkNervSoC is a BSV version of nervsoc.sv

// nervsoc.sv is from:    https://github.com/YosysHQ/nerv

// ================================================================
// Import from BSV library

import RegFile :: *;
import I2C :: *;
// ================================================================
// Local imports

import Nerv :: *;

// ================================================================
// A small NERV SoC

interface NervSoC_IFC;
   method Bit #(32) gpio;
   // TX -> a byte to be send
   method ActionValue#(Bit #(8)) get_uart_tx_byte;
   // RX -> a byte to be received
   method Action set_uart_rx_byte(Bit #(8) rx);
   // I2C methods
   method ActionValue #(I2CRequest) i2c_get_request;
   method Action i2c_give_response(I2CResponse r);
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
   Bit #(32) gpio_addr = 32'h 0100_0000;
   // I2c Order of operations:
   // 1) Copy data to i2c_reg_data
   // 2) Write addr to i2c_reg_addr
   // 3) Writing to i2c_reg_addr initiates transaction
   // 4) Once i2c_reg_status & I2C_COMPLETE_BIT is 1(True) resulting data
   // are stored in i2c_reg_data (in case on Read transaction)
   // 5) i2c_reg_status holds also errors about the transaction
   // for example `if (i2c_reg_status & I2C_TRANSACTION_ERROR)` then an error occured
   // TODO: add granularity into error reporting (arbitration, no slave ack, etc)
   //
   // 7bits addr, 1bit RW, 8bits total - the firmware is responsible for setting R/W bit
   Bit #(32) i2c_reg_addr = 32'h 0300_0000;
   // I2C fifo has up to 16 bytes (4 registers)
   Bit #(32) i2c_reg_data = 32'h 0300_0004;
   // I2C status reg (transaction complete 1bit, transaction error 1bit, error type 2bits)
   Bit #(32) i2c_reg_status = 32'h 0300_0008;

   Bit #(32) uart_reg_addr_tx = 32'h 0200_0000;
   Bit #(32) uart_reg_addr_rx = 32'h 0200_0004;
   Bit #(32) uart_reg_addr_data_ready = 32'h 0200_0008;

   // IO registers
   Reg #(Bit #(32)) rg_gpio       <- mkRegU;
   Reg #(Bit #(8)) rg_uart_tx <- mkReg(0);
   Reg #(Bit #(8)) rg_uart_rx <- mkReg(0);
   Reg #(Bool) rg_uart_rx_data_ready <- mkReg(False);
   Reg #(Bool) rg_uart_tx_data_ready <- mkReg(False);
   Reg #(Bit #(8)) rg_i2c_addr <- mkReg(0);
   Reg #(Bit #(32)) rg_i2c_data <- mkReg(0);
   Reg #(Bit #(32)) rg_i2c_status <- mkReg(0);
   Reg #(Bool) rg_i2c_transaction_ready <- mkReg(False);
   Reg #(Bool) rg_i2c_transaction_complete <- mkReg(False);

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
         // Write to GPIO pins
         gpio_addr:
            begin
               rg_gpio <= ((rg_gpio & (~ mask)) | (wdata & mask));
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
               // Only 8 bytes for the address, the rest is ignored
               rg_i2c_addr <= wdata[7:0];
               rg_i2c_transaction_ready <= True;
            end
         i2c_reg_data:
            begin
               rg_i2c_data <= ((rg_i2c_data & (~ mask)) | (wdata & mask));
            end
         i2c_reg_status:
            begin
               rg_dmem_rdata <= rg_i2c_status;
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
   // set GPIO
   method Bit #(32) gpio = rg_gpio;

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

   // I2C methods
   method ActionValue #(I2CRequest) i2c_get_request () if (rg_i2c_transaction_ready);
      begin
         let r =  I2CRequest {
               write: unpack(rg_i2c_addr[0]),
               address: rg_i2c_addr[7:0], // Unclear what this is for
               slaveaddr: rg_i2c_addr[7:1],
               data: rg_i2c_data[7:0]
            };
         return r;
      end
   endmethod

   method Action i2c_give_response(I2CResponse r);
      begin
         rg_i2c_data <= signExtend(r.data);
         rg_i2c_transaction_complete <= True;
      end
   endmethod

endmodule

// ================================================================

endpackage
