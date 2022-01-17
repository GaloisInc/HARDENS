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

// ================================================================
// Top

(* synthesize *)
module mkTop (Empty);

   Reg #(Bit #(32)) rg_leds <- mkReg (0);

   NervSoC_IFC nerv_soc <- mkNervSoC;

   rule rl_leds;
      let leds = nerv_soc.leds;
      if (leds != rg_leds) $display ("LEDs: %032b", leds);

      rg_leds <= leds;
   endrule
endmodule

// ================================================================
