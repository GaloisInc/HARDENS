import NervSoC :: *;

// ================================================================
// Top

(* synthesize *)
module mkTop (Empty);
   NervSoC_IFC nerv_soc <- mkNervSoC;

   rule rl_leds;
      let leds = nerv_soc.leds;
      $display ("LEDs: %0b", leds);
   endrule
endmodule

// ================================================================
