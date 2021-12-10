#include <verilated.h>          // Defines common routines
#include <iostream>             // Need std::cout
#include "VmkNervSoC.h"               // From Verilating "top.v"

VmkNervSoC *top;                      // Instantiation of model

vluint64_t main_time = 0;       // Current simulation time
// This is a 64-bit integer to reduce wrap over issues and
// allow modulus.  This is in units of the timeprecision
// used in Verilog (or from --timescale-override)

double sc_time_stamp() {        // Called by $time in Verilog
    return main_time;           // converts to double, to match
                                // what SystemC does
}

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);   // Remember args

    top = new VmkNervSoC();             // Create model

    //top->reset_l = 0;           // Set some inputs

    while (!Verilated::gotFinish()) {
        // if (main_time > 10) {
        //     top->reset_l = 1;   // Deassert reset
        // }
        if ((main_time % 10) == 1) {
            top->CLK = 1;       // Toggle clock
        }
        if ((main_time % 10) == 6) {
            top->CLK = 0;
        }
        if ((main_time % 12000000) == 0) {
            std::cout << main_time << std::endl;       // Read a output
            printf("LEDs: [%x,%x]\n", top->RDY_leds,top->leds);
        }
        top->eval();            // Evaluate model
        
        main_time++;            // Time passes...
    }

    top->final();               // Done simulating
    //    // (Though this example doesn't get here)
    delete top;
}