module Coincidence_2_4
    ( input logic [31:0] x,
      output logic out
    );
    logic a;
    logic b;
    logic c;
    logic d;
    // ../models/RTS/ActuationUnit.cry:74:7--74:8
    assign a = x[31:24] != 8'h0;
    // ../models/RTS/ActuationUnit.cry:75:7--75:8
    assign b = x[23:16] != 8'h0;
    // ../models/RTS/ActuationUnit.cry:76:7--76:8
    assign c = x[15:8] != 8'h0;
    // ../models/RTS/ActuationUnit.cry:77:7--77:8
    assign d = x[7:0] != 8'h0;
    // ../models/RTS/ActuationUnit.cry:71:3--71:18
    assign out = a & b | ((a | b) & (c | d) | c & d);
endmodule
module TemperatureLogic
    ( input logic [31:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:58:1--58:17
    Coincidence_2_4 Coincidence_2_4_inst1 (.x(ts),
                                           .out(out));
endmodule
module PressureLogic
    ( input logic [31:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:61:1--61:14
    Coincidence_2_4 Coincidence_2_4_inst1 (.x(ts),
                                           .out(out));
endmodule
module TempPressureTripOut
    ( input logic [1:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:67:1--67:20
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
    // ../models/RTS/ActuationUnit.cry:48:5--48:21
    assign temperatureTrips[31:0] = trips[95:64];
    // ../models/RTS/ActuationUnit.cry:49:5--49:18
    assign pressureTrips[31:0] = trips[63:32];
    // ../models/RTS/ActuationUnit.cry:46:5--46:7
    logic TemperatureLogic_out;
    TemperatureLogic TemperatureLogic_inst1 (.ts(temperatureTrips),
                                             .out(TemperatureLogic_out));
    logic PressureLogic_out;
    PressureLogic PressureLogic_inst1 (.ts(pressureTrips),
                                       .out(PressureLogic_out));
    TempPressureTripOut TempPressureTripOut_inst1 (.ts({TemperatureLogic_out, PressureLogic_out}),
                                                   .out(d0));
    // ../models/RTS/ActuationUnit.cry:44:1--44:11
    assign out = d0 | old;
endmodule
module SaturationLogic
    ( input logic [31:0] ts,
      output logic out
    );
    // ../models/RTS/ActuationUnit.cry:64:1--64:16
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
    // ../models/RTS/ActuationUnit.cry:55:5--55:20
    assign saturationTrips[31:0] = trips[31:0];
    // ../models/RTS/ActuationUnit.cry:54:5--54:7
    SaturationLogic SaturationLogic_inst1 (.ts(saturationTrips),
                                           .out(d1));
    // ../models/RTS/ActuationUnit.cry:52:1--52:11
    assign out = d1 | old;
endmodule
