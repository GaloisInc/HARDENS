module ActuateDevice
    ( input logic [1:0] vs,
      output logic out
    );
    // ../models/RTS/Actuation.cry:25:1--25:14
    assign out = vs[1] | vs[0];
endmodule
