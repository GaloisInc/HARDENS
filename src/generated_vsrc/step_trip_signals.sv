module Is_Ch_Tripped
    #(localparam lg2 = 2)
    ( input logic [lg2 - 1:0] mode,
      input logic sensor_tripped,
      output logic out
    );
    // ../models/RTS/Instrumentation.cry:93:1--93:14
    // ../models/RTS/Instrumentation.cry:96:3--96:49
    assign out = (mode == 2'h2) | (mode == 2'h1) & sensor_tripped;
endmodule
module Generate_Sensor_Trips
    #(localparam NChannels = 3)
    ( input logic [NChannels * 32 - 1:0] vals,
      input logic [NChannels * 32 - 1:0] setpoints,
      output logic [NChannels - 1:0] out
    );
    // ../models/RTS/Instrumentation.cry:102:1--102:22
    // ../models/RTS/Instrumentation.cry:103:3--108:41
    // ../models/RTS/Instrumentation.cry:103:3--103:47
    genvar gv0;
    for (gv0 = 0; gv0 < NChannels; gv0 = gv0 + 1)
      begin: for_blk
        logic [1:0] ch;
        assign ch[1:0] = gv0 % 3;
        // ../models/RTS/Instrumentation.cry:103:5--103:11
        // ../models/RTS/Instrumentation.cry:106:14--108:41
        // ../models/RTS/Instrumentation.cry:106:14--106:48
        logic [1:0] ch1;
        logic [31:0] v;
        logic [31:0] sp;
        // ../models/RTS/Instrumentation.cry:106:9--106:11
        // ../models/RTS/Instrumentation.cry:103:9--103:11
        assign ch1[1:0] = ch;
        // ../models/RTS/Instrumentation.cry:107:22--107:23
        // ../models/RTS/Instrumentation.cry:107:27--107:36
        assign v[31:0] = vals[32 * (NChannels - ch1 - 1) + 31-:32];
        // ../models/RTS/Instrumentation.cry:108:22--108:24
        // ../models/RTS/Instrumentation.cry:108:27--108:41
        assign sp[31:0] = setpoints[32 * (NChannels - ch1 - 1) + 31-:32];
        assign out[NChannels - gv0 - 1] = ch1 == 2'h2 ? v < sp : sp < v;
      end: for_blk
endmodule
