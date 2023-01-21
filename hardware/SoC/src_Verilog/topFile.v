// Copyright 2021, 2022, 2023 Galois, Inc.
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

module top(
    input clkin,
    input RST_N,
    output [0:7] leds,
    output clkout,
    input uart_rx,
    output uart_tx,
    //input output sda,
    //output scl,
    );

// PLL might not be needed, as we get 12MHz directly from
// the FTDI clock (requires an active JTAG connection)
// pll_12_50 pll(
//     .clki(clkin),
//     .clko(clk)
// );

wire SIN, SOUT;

mkFpgaTop_IFC fpga(clkin,
    RST_N,
//    .SDA(sda),
//    .SCL(scl),
    SIN,
    SOUT,
    leds
);

assign SIN = uart_rx;
assign SOUT = uart_tx;
assign clkout = clkin;

endmodule
