// Copyright (c) 2022 Rishiyur S. Nikhil

// ================================================================
// Top-level module instantiates NervSoC and displays the LED outputs
// whenever they change.

// ================================================================
// Import from BSV library

// None

// ================================================================
// Local imports

import NervSoC :: *;

// IO
import I2C :: *;
import RS232 :: *;
import GetPut::*;

// This define marks simulation
// TODO: create a switch in the makefile
`define SIMULATION

// ================================================================
// Top

// This works only if I simulate with iVerilog
import "BDPI" function Action c_putchar (Bit #(8) c);
import "BDPI" function ActionValue #(Bit #(8)) c_trygetchar (Bit #(8) dummy);


(* synthesize *)
module mkTop (Empty);

   Reg #(Bit #(32)) rg_leds <- mkReg (0);

   NervSoC_IFC nerv_soc <- mkNervSoC;

   // I/O peripherals
   // @podhrmic TODO: check the prescalers
   // and look into proper use of I2C module
   // I2CController #(1) i2c_controller <- mkI2CController();
   UART #(4) uart <- mkUART(8, NONE, STOP_1, 16);

   // ================================================================
   // UART console I/O
   // Based on https://github.com/bluespec/Piccolo/blob/master/src_Testbench/Top/Top_HW_Side.bsv
   //
   // Poll terminal input and relay any chars into system console input.
   // Note: rg_console_in_poll is used to poll only every N cycles, whenever it wraps around to 0.
   // Note: if the SoC starts dropping bytes, try increasing the register size
`ifdef SIMULATION
   begin
   Reg #(Bit #(12)) rg_console_in_poll <- mkReg (0);
   rule uart_rx;
      if (rg_console_in_poll == 0) begin
         Bit #(8) ch <- c_trygetchar (?);
         if (ch != 0) begin
            nerv_soc.set_uart_rx_byte(ch);
         end
      end
      rg_console_in_poll <= rg_console_in_poll + 1;
   endrule
   end
`else
   begin
   rule uart_rx;
      if (rg_console_in_poll == 0) begin
         Bit #(8) ch <- uart.tx.get();
         if (ch != 0) begin
            nerv_soc.set_uart_rx_byte(ch);
         end
      end
   endrule
   end
`endif

   rule uart_tx;
      let val <-  nerv_soc.get_uart_tx_byte();
`ifdef SIMULATION
      c_putchar(val);
`else
      uart.rx.put(val);
`endif
   endrule

   rule rl_leds;
      let leds = nerv_soc.leds;
      if (leds != rg_leds) $display ("LEDs: %032b", leds);
      rg_leds <= leds;
   endrule

endmodule

// ================================================================
