module Generate_Sensor_Trips
    #(localparam NChannels = 3)
    ( input logic [NChannels * 32 - 1:0] vals,
      input logic [NChannels * 32 - 1:0] setpoints,
      output logic [NChannels - 1:0] out
    );
    // ../models/RTS/Instrumentation.cry:149:1--149:22
    // ../models/RTS/Instrumentation.cry:150:3--155:41
    // ../models/RTS/Instrumentation.cry:150:3--150:47
    genvar gv0;
    for (gv0 = 0; gv0 < NChannels; gv0 = gv0 + 1)
      begin: for_blk
        logic [1:0] ch;
        assign ch[1:0] = gv0 % 3;
        // ../models/RTS/Instrumentation.cry:150:5--150:11
        // ../models/RTS/Instrumentation.cry:153:14--155:41
        // ../models/RTS/Instrumentation.cry:153:14--153:48
        logic [1:0] ch1;
        logic [31:0] v;
        logic [31:0] sp;
        // ../models/RTS/Instrumentation.cry:153:9--153:11
        // ../models/RTS/Instrumentation.cry:150:9--150:11
        assign ch1[1:0] = ch;
        // ../models/RTS/Instrumentation.cry:154:22--154:23
        // ../models/RTS/Instrumentation.cry:154:27--154:36
        assign v[31:0] = vals[32 * (NChannels - ch1 - 1) + 31-:32];
        // ../models/RTS/Instrumentation.cry:155:22--155:24
        // ../models/RTS/Instrumentation.cry:155:27--155:41
        assign sp[31:0] = setpoints[32 * (NChannels - ch1 - 1) + 31-:32];
        assign out[NChannels - gv0 - 1] = ch1 == 2'h2 ? v < sp : sp < v;
      end: for_blk
endmodule
module Is_Ch_Tripped
    #(localparam lg2 = 2)
    ( input logic [lg2 - 1:0] mode,
      input logic sensor_tripped,
      output logic out
    );
    // ../models/RTS/Instrumentation.cry:140:1--140:14
    // ../models/RTS/Instrumentation.cry:143:3--143:49
    assign out = (mode == 2'h2) | (mode == 2'h1) & sensor_tripped;
endmodule
