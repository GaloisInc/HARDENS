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

(* synthesize *)
module mkTop (Empty);

   Reg #(Bit #(32)) rg_leds <- mkReg (0);

   NervSoC_IFC nerv_soc <- mkNervSoC;


   // I/O peripherals
   // @podhrmic TODO: check the prescalers
   //I2C i2c <- mkI2C(16);
   UART #(4) uart <- mkUART(8, NONE, STOP_1, 16);

   rule uart_tx;
      let val <-  nerv_soc.get_uart_tx_byte();
      uart.rx.put(val);
      $write("%c",val);
   endrule

   rule uat_rx;
      let val <- uart.tx.get();
      nerv_soc.set_uart_rx_byte(val);
   endrule

   rule rl_leds;
      let leds = nerv_soc.leds;
      if (leds != rg_leds) $display ("LEDs: %032b", leds);

      rg_leds <= leds;
   endrule


endmodule

// ================================================================
