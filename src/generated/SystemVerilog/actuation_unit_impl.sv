module Coincidence_2_4
    ( input logic [31:0] x,
      output logic out
    );
    logic a;
    logic b;
    logic c;
    logic d;
    // ../models/RTS/ActuationUnit.cry:60:7--60:8
    assign a = x[31:24] != 8'h0;
    // ../models/RTS/ActuationUnit.cry:61:7--61:8
    assign b = x[23:16] != 8'h0;
    // ../models/RTS/ActuationUnit.cry:62:7--62:8
    assign c = x[15:8] != 8'h0;
    // ../models/RTS/ActuationUnit.cry:63:7--63:8
    assign d = x[7:0] != 8'h0;
    // ../models/RTS/ActuationUnit.cry:57:3--57:18
    assign out = a & b | ((a | b) & (c | d) | c & d);
endmodule
module TemperatureLogic
    ( input logic [31:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:44:1--44:17
    Coincidence_2_4 Coincidence_2_4_inst1 (.x(ts),
                                           .out(out));
endmodule
module PressureLogic
    ( input logic [31:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:47:1--47:14
    Coincidence_2_4 Coincidence_2_4_inst1 (.x(ts),
                                           .out(out));
endmodule
module TempPressureTripOut
    ( input logic [1:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:53:1--53:20
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
    // ../models/RTS/ActuationUnit.cry:34:5--34:21
    assign temperatureTrips[31:0] = trips[95:64];
    // ../models/RTS/ActuationUnit.cry:35:5--35:18
    assign pressureTrips[31:0] = trips[63:32];
    // ../models/RTS/ActuationUnit.cry:32:5--32:7
    logic TemperatureLogic_out;
    TemperatureLogic TemperatureLogic_inst1 (.ts(temperatureTrips),
                                             .out(TemperatureLogic_out));
    logic PressureLogic_out;
    PressureLogic PressureLogic_inst1 (.ts(pressureTrips),
                                       .out(PressureLogic_out));
    TempPressureTripOut TempPressureTripOut_inst1 (.ts({TemperatureLogic_out, PressureLogic_out}),
                                                   .out(d0));
    // ../models/RTS/ActuationUnit.cry:30:1--30:11
    assign out = d0 | old;
endmodule
module SaturationLogic
    ( input logic [31:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:50:1--50:16
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
    // ../models/RTS/ActuationUnit.cry:41:5--41:20
    assign saturationTrips[31:0] = trips[31:0];
    // ../models/RTS/ActuationUnit.cry:40:5--40:7
    SaturationLogic SaturationLogic_inst1 (.ts(saturationTrips),
                                           .out(d1));
    // ../models/RTS/ActuationUnit.cry:38:1--38:11
    assign out = d1 | old;
endmodule
