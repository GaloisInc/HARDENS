// Copyright (c) 2016-2019 Bluespec, Inc.  All Rights Reserved
// Original source: https://github.com/bluespec/Piccolo/tree/master/builds/Resources/Verilator_resources
// Modified by @podhrmic

// import "BDPI" function Action c_tx (Bit #(8)  char);
import "DPI-C"
//function  int unsigned  c_putchar (byte unsigned  ch);
function  void  c_putchar (byte unsigned  ch);

// import "BDPI" function ActionValue #(Bit #(8)) c_rx ();
import "DPI-C"
function  byte unsigned  c_trygetchar (byte unsigned dummy);

import "DPI-C"
function  byte unsigned  c_i2c_request (byte unsigned slaveaddr,
                                        byte unsigned data);
