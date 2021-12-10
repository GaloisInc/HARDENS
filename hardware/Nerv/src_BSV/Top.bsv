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

   Reg#(int) cycles <- mkReg(0);
   rule timeout;
       let timeout = 10;
       cycles <=cycles + 1;
       if (cycles > timeout)
       begin
           $display("Simulated %0d cycles", cycles);
           $finish(2);
       end
   endrule
endmodule

// ================================================================
