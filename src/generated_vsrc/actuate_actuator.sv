module ActuateActuator
    ( input logic [1:0] inputs,
      output logic out
    );
    // ../models/RTS/Actuator.cry:21:1--21:16
    assign out = inputs[1] | inputs[0];
endmodule
