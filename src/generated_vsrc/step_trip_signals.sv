module Is_Ch_Tripped
    #(localparam lg2 = 2)
    ( input logic [lg2 - 1:0] mode,
      input logic sensor_tripped,
      output logic out
    );
    // ../models/RTS/InstrumentationUnit.cry:129:1--129:14
    assign out = (mode == 2'h2) | (mode == 2'h1) & sensor_tripped;
endmodule
module Generate_Sensor_Trips
    #(localparam NChannels = 3)
    ( input logic [NChannels * 32 - 1:0] vals,
      input logic [NChannels * 32 - 1:0] setpoints,
      output logic [NChannels - 1:0] out
    );
    // ../models/RTS/InstrumentationUnit.cry:213:3--213:24
    // ../models/RTS/InstrumentationUnit.cry:214:5--219:43
    // ../models/RTS/InstrumentationUnit.cry:214:5--214:49
    genvar gv0;
    for (gv0 = 0; gv0 < NChannels; gv0 = gv0 + 1)
      begin: for_blk
        logic [1:0] ch;
        assign ch[1:0] = gv0 % 3;
        // ../models/RTS/InstrumentationUnit.cry:217:16--219:43
        // ../models/RTS/InstrumentationUnit.cry:217:16--217:51
        logic [31:0] v;
        logic [31:0] sp;
        // ../models/RTS/InstrumentationUnit.cry:218:24--218:25
        assign v[31:0] = vals[32 * (NChannels - ch - 1) + 31-:32];
        // ../models/RTS/InstrumentationUnit.cry:219:24--219:26
        assign sp[31:0] = setpoints[32 * (NChannels - ch - 1) + 31-:32];
        assign out[NChannels - gv0 - 1] = ch == 2'h2 ? $signed(v) < $signed(sp) : sp < v;
      end: for_blk
endmodule
