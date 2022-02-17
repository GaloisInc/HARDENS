module Coincidence_2_4
    ( input logic [31:0] x,
      output logic out
    );
    logic [3:0] bits;
    // ../models/RTS/ActuationUnit.cry:35:7--35:11
    // ../models/RTS/ActuationUnit.cry:35:14--35:33
    genvar gv0;
    for (gv0 = 0; gv0 < 4; gv0 = gv0 + 1)
      begin: for_blk
        logic [7:0] b;
        assign b[7:0] = x[8 * (3 - gv0 % 4) + 7-:8];
        assign bits[3 - gv0] = b != 8'h0;
      end: for_blk
    // ../models/RTS/ActuationUnit.cry:33:3--33:18
    assign out = (bits != 4'h0) & ((bits != 4'h1) & ((bits != 4'h2) & ((bits != 4'h4) & (bits != 4'h8))));
endmodule
module SaturationLogic
    ( input logic [31:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:26:1--26:16
    Coincidence_2_4 Coincidence_2_4_inst1 (.x(ts),
                                           .out(out));
endmodule
module Actuate_D1
    ( input logic [95:0] trips,
      input logic old,
      output logic out
    );
    logic [31:0] saturationTrips;
    logic d1;
    // ../models/RTS/ActuationUnit.cry:94:7--94:22
    assign saturationTrips[31:0] = trips[31:0];
    // ../models/RTS/ActuationUnit.cry:93:7--93:9
    SaturationLogic SaturationLogic_inst1 (.ts(saturationTrips),
                                           .out(d1));
    // ../models/RTS/ActuationUnit.cry:91:3--91:13
    assign out = d1 | old;
endmodule
module TemperatureLogic
    ( input logic [31:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:20:1--20:17
    Coincidence_2_4 Coincidence_2_4_inst1 (.x(ts),
                                           .out(out));
endmodule
module PressureLogic
    ( input logic [31:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:23:1--23:14
    Coincidence_2_4 Coincidence_2_4_inst1 (.x(ts),
                                           .out(out));
endmodule
module TempPressureTripOut
    ( input logic [1:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:29:1--29:20
    assign out = ts[1] | ts[0];
endmodule
module Actuate_D0
    ( input logic [95:0] trips,
      input logic old,
      output logic out
    );
    logic [31:0] temperatureTrips;
    logic [31:0] pressureTrips;
    logic d0;
    // ../models/RTS/ActuationUnit.cry:87:7--87:23
    assign temperatureTrips[31:0] = trips[95:64];
    // ../models/RTS/ActuationUnit.cry:88:7--88:20
    assign pressureTrips[31:0] = trips[63:32];
    // ../models/RTS/ActuationUnit.cry:85:7--85:9
    logic TemperatureLogic_out;
    TemperatureLogic TemperatureLogic_inst1 (.ts(temperatureTrips),
                                             .out(TemperatureLogic_out));
    logic PressureLogic_out;
    PressureLogic PressureLogic_inst1 (.ts(pressureTrips),
                                       .out(PressureLogic_out));
    TempPressureTripOut TempPressureTripOut_inst1 (.ts({TemperatureLogic_out, PressureLogic_out}),
                                                   .out(d0));
    // ../models/RTS/ActuationUnit.cry:83:3--83:13
    assign out = d0 | old;
endmodule
