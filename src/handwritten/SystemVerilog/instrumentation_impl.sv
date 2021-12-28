module Is_Ch_Tripped
    #(localparam Log2Modes = 2)
    ( input logic [Log2Modes - 1:0] mode,
      input logic sensor_tripped,
      output logic out
    );
   assign out = (mode == 2) || ((mode == 1) & sensor_tripped);
endmodule

module Generate_Sensor_Trips
    #(localparam NChannels = 3)
    ( input logic [NChannels * 32 - 1:0] vals,
      input logic [NChannels * 32 - 1:0] setpoints,
      output logic [NChannels - 1:0] out
    );
   genvar ch;
   for (ch = 0; ch < NChannels; ch = ch + 1) begin
      localparam rev_ch = NChannels - ch - 1;
      logic [31:0]v  = vals[(rev_ch*32) + 31 -: 32];
      logic [31:0]sp = setpoints[(rev_ch*32) + 31 -: 32];
      // SAW caught a bug here, originally used
      // `rev_ch` in the conditional
      if (ch == 2) begin
         assign out[rev_ch] = $signed(v) < $signed(sp);
      end else begin
         assign out[rev_ch] = sp < v;
      end
   end
endmodule
