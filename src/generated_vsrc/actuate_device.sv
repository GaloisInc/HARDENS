module Actuate_Device
    ( input logic [1:0] vs,
      output logic out
    );
    // ../models/RTS/Actuation.cry:42:1--42:15
    assign out = vs[1] | vs[0];
endmodule
