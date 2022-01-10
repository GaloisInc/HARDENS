module Is_Ch_Tripped
    #(localparam lg2 = 2)
    ( input logic [lg2 - 1:0] mode,
      input logic sensor_tripped,
      output logic out
    );
    // ../models/RTS/InstrumentationUnit.cry:129:1--129:14
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
    // ../models/RTS/InstrumentationUnit.cry:222:11--222:12
    assign v[31:0] = vals[32 * (NChannels - ch - 1) + 31-:32];
    // ../models/RTS/InstrumentationUnit.cry:223:11--223:13
    assign sp[31:0] = setpoints[32 * (NChannels - ch - 1) + 31-:32];
    // ../models/RTS/InstrumentationUnit.cry:221:3--221:7
    assign out = ch == 2'h2 ? $signed(v) < $signed(sp) : sp < v;
endmodule
module Generate_Sensor_Trips
    #(localparam NChannels = 3)
    ( input logic [NChannels * 32 - 1:0] vals,
      input logic [NChannels * 32 - 1:0] setpoints,
      output logic [NChannels - 1:0] out
    );
    logic t;
    logic p;
    logic s;
    // ../models/RTS/InstrumentationUnit.cry:215:7--215:8
    Trip Trip_inst1 (.vals(vals),
                     .setpoints(setpoints),
                     .ch(2'h0),
                     .out(t));
    // ../models/RTS/InstrumentationUnit.cry:216:7--216:8
    Trip Trip_inst2 (.vals(vals),
                     .setpoints(setpoints),
                     .ch(2'h1),
                     .out(p));
    // ../models/RTS/InstrumentationUnit.cry:217:7--217:8
    Trip Trip_inst3 (.vals(vals),
                     .setpoints(setpoints),
                     .ch(2'h2),
                     .out(s));
    // ../models/RTS/InstrumentationUnit.cry:213:3--213:24
    assign out[NChannels - 1] = t;
    assign out[NChannels - 2] = p;
    assign out[NChannels - 3] = s;
endmodule
