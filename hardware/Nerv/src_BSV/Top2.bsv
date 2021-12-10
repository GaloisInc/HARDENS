import Nerv :: *;

// ================================================================
// Top

(* synthesize *)
module mkTop (Empty);
   Nerv_IFC nerv <- mkNerv;

   rule mainrule;
      nerv.m_stall (False);
      nerv.m_dmem_rdata (0);
      nerv.m_imem_data (0);
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
