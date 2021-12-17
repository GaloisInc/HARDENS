# RTS implementation sources

This directory contains the source (both hand-written and generated, `C` and
`SystemVerilog`) for the reactor trip system:

- The root directory contains hand-written `C` sources
- [](./generated_csrc) contains `C` sources generated from the `Cryptol` model
- [](./generated_vsrc) contains `SystemVerilog` sources generated from the `Cryptol` model

## Dependencies

Besides a normal `clang` toolchain, the `Makefile` targets depend on the following tools:

- `cryptol-verilogc` <https://gitlab-ext.galois.com/cryptol/cryptol-verilog>
- `crymp` <https://gitlab-ext.galois.com/cryptol/cryptol-codegen/-/tree/hardens-tweaks> 
- `verilator` <https://www.veripool.org/verilator/>

## Implementation status

### Simulation Targets
The `Makefile` in this directory can generate simulation builds of the `RTS`
that execute on the host system, controllable via the command-line/stdin. The two targets of interest are:

- `rts.posix`: which is built using implementations from the generated `C` sources; and
- `rts.posix.verilog`: which builds the simulator against verilator

Currently the simulator uses `getline` to retrieve user input: since this is
blocking, it might appear that the system does not respond immediately to user
input. Hitting `return` will cause the UI to update.

An example of how to script the system is given in [](tests/sense_actuate_0); you can execute

``` sh
cat tests/sense_actuate_0 | ./rts.posix
```

to run the script.

### Notes and Current Limitations

- Currently the simulator build does *not* model failure or other exceptional conditions.
- The self-test functionality is not yet implemented.
- Hand-written equivalents of the generated `C` and `SystemVerilog` are not yet included.
- The build system does not yet support mixing implementations of different components.


## Building

Run `make rts.posix{.verilog}` to generate an executable simulator. To regenerate
`SystemVerilog` or `C` functions after an update to the Cryptol model, you can
run `REGEN_SOURCES=1 make <target>`; by default, the checked-in existing
generated code will be used.
