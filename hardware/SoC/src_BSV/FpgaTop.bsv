// Copyright 2021, 2022, 2023 Galois, Inc.
// Copyright 2022 Rishiyur Nikhil
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

import NervSoC :: *;

// IO
import I2C :: *;
import RS232 :: *;
import GetPut::*;

interface FpgaTop_IFC;
    (* prefix = "" *)
    interface RS232 rs232;
    //(* prefix = "" *)
    //interface I2C_Pins i2c;
    (* always_ready *)
    method Bit#(8) leds();
endinterface

(* synthesize *)
module mkFpgaTop_IFC(FpgaTop_IFC);
    // Divisor of 10 for baudrate of 76800
    UART #(4) uart <- mkUART(8, NONE, STOP_1, 10);
    //I2CController #(1) i2c_controller <- mkI2CController();

    NervSoC_IFC nerv_soc <- mkNervSoC;

    rule uart_transmit;
        let val <-  nerv_soc.get_uart_tx_byte();
        uart.rx.put(val);
    endrule

    Reg #(Bit #(12)) rg_console_in_poll <- mkReg (0);
    rule uart_receive;
        if (rg_console_in_poll == 0) begin
           Bit #(8) ch <- uart.tx.get();
           if (ch != 0) begin
              nerv_soc.set_uart_rx_byte(ch);
           end
        end
        rg_console_in_poll <= rg_console_in_poll + 1;
    endrule

    

    interface rs232 = uart.rs232;
    // TODO: i2c interface
    //interface I2C_Pins i2c = i2c_controller.i2c;
    method leds = nerv_soc.gpio;
endmodule
