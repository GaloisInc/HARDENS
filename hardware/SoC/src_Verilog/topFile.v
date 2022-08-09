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