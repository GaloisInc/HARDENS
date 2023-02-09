module ActuateActuator
    ( input logic [1:0] inputs,
      output logic out
    );
    // ../models/RTS/Actuator.cry:45:1--45:16
    assign out = inputs[1] | inputs[0];
endmodule
