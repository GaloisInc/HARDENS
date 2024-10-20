module Is_Ch_Tripped
    #(localparam lg2 = 2)
    ( input logic [lg2 - 1:0] mode,
      input logic sensor_tripped,
      output logic out
    );
    // ../models/RTS/InstrumentationUnit.cry:153:1--153:14
    assign out = (mode == 2'h2) | (mode == 2'h1) & sensor_tripped;
endmodule
module Trip
    #(localparam NChannels = 3,
      localparam lg2 = 2)
    ( input logic [NChannels * 32 - 1:0] vals,
      input logic [NChannels * 32 - 1:0] setpoints,
      input logic [lg2 - 1:0] ch,
      output logic out
    );
    logic [31:0] v;
    logic [31:0] sp;
    // ../models/RTS/InstrumentationUnit.cry:242:9--242:10
    assign v[31:0] = vals[32 * (NChannels - ch - 1) + 31-:32];
    // ../models/RTS/InstrumentationUnit.cry:243:9--243:11
    assign sp[31:0] = setpoints[32 * (NChannels - ch - 1) + 31-:32];
    // ../models/RTS/InstrumentationUnit.cry:241:1--241:5
    assign out = ch == 2'h2 ? $signed(v) < $signed(sp) : sp < v;
endmodule
module Generate_Sensor_Trips
    #(localparam NChannels = 3)
    ( input logic [NChannels * 32 - 1:0] vals,
      input logic [NChannels * 32 - 1:0] setpoints,
      output logic [NChannels - 1:0] out
    );
    // ../models/RTS/InstrumentationUnit.cry:235:1--235:22
    // ../models/RTS/InstrumentationUnit.cry:238:5--238:76
    Trip Trip_inst1 (.vals(vals),
                     .setpoints(setpoints),
                     .ch(2'h0),
                     .out(out[NChannels - 1]));
    Trip Trip_inst2 (.vals(vals),
                     .setpoints(setpoints),
                     .ch(2'h1),
                     .out(out[NChannels - 2]));
    Trip Trip_inst3 (.vals(vals),
                     .setpoints(setpoints),
                     .ch(2'h2),
                     .out(out[NChannels - 3]));
endmodule
