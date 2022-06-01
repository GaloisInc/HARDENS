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


// ================================================================
// Top

import "BDPI" function Action c_putchar (Bit #(8) c);
import "BDPI" function ActionValue #(Bit #(8)) c_trygetchar (Bit #(8) dummy);
import "BDPI" function ActionValue #(Bit #(8)) c_i2c_request (Bit #(8) addr,
                                                              Bit #(8) data);

(* clock_prefix="CLK", reset_prefix="RST_N" *)
(* synthesize *)
module mkTop (Empty);

   Reg #(Bit #(8)) rg_gpio <- mkReg (0);

   NervSoC_IFC nerv_soc <- mkNervSoC;

   // I/O peripherals
   // @podhrmic TODO: check the prescalers
   // and look into proper use of I2C module
   I2CController #(1) i2c_controller <- mkI2CController();
   UART #(4) uart <- mkUART(8, NONE, STOP_1, 16);
   //uart.RS232.sout ?

   // ================================================================
   // UART console I/O
   // Based on https://github.com/bluespec/Piccolo/blob/master/src_Testbench/Top/Top_HW_Side.bsv
   //
   // Poll terminal input and relay any chars into system console input.
   // Note: rg_console_in_poll is used to poll only every N cycles, whenever it wraps around to 0.
   // Note: if the SoC starts dropping bytes, try increasing the register size
   Reg #(Bit #(12)) rg_console_in_poll <- mkReg (0);
`ifdef SIMULATION
   begin
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
   // FPGA
   begin
   rule uart_rx;
      if (rg_console_in_poll == 0) begin
         Bit #(8) ch <- uart.tx.get();
         if (ch != 0) begin
            nerv_soc.set_uart_rx_byte(ch);
         end
      end
      rg_console_in_poll <= rg_console_in_poll + 1;
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

   Reg #(Bit #(8)) rg_i2c_resp <- mkRegU();
   Reg #(Bool) rg_i2c_complete <- mkReg(False);
   rule i2c_request(!rg_i2c_complete);
      let request <- nerv_soc.i2c_get_request();
      let val <- c_i2c_request(request.address, request.data);
      rg_i2c_resp <= val;
      rg_i2c_complete <= True;
   endrule

   rule i2c_response(rg_i2c_complete);
      let response = I2CResponse { data: rg_i2c_resp};
      nerv_soc.i2c_give_response(response);
      rg_i2c_complete <= False;
   endrule

   rule rl_leds;
      let gpio = nerv_soc.gpio;
      if (gpio != rg_gpio) $display ("GPIO: %032b", gpio);
      rg_gpio <= gpio;
   endrule

endmodule

// ================================================================
