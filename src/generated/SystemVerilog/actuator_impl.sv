module ActuateActuator
    ( input logic [1:0] inputs,
      output logic out
    );
    // ../models/RTS/Actuator.cry:31:1--31:16
    assign out = inputs[1] | inputs[0];
endmodule
