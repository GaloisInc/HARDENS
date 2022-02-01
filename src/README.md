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
- `verilator` <https://www.veripool.org/verilator/> *Note* on macOS (tested on
  11.6.1) it seems there is an issue with recent versions: version 4.108 seems
  to work.
  
Verification with `frama-c` additionally requires `frama-c` version 24.0
<https://frama-c.com>.

## Implementation status

The RTS can be built for simulation on a macOS or Linux host, or (not yet
implemented) on a NERV-based SoC.

### Simulation Targets

The `Makefile` in this directory can generate simulation builds of the `RTS`
that execute on the host system, controllable via the command-line/stdin. 

#### Execution

The `PLATFORM` variable controls whether or not we are building for the Soc:

- `PLATFORM=Host` builds the rts for a POSIX system
  * When `Platform=Host`, the build system can be configured to simulate the concurrency of the
    NERV-SoC using `pthreads` by setting `EXECUTION=Parallel` (set by default). `Execution=Sequential` 
    simulates the system with a single thread of execution and single fixed schedule of task interleavings.
- `Platform=NERV` builds the rts for the NERV-based SoC (not yet implemented)


#### Sensors

The simulation build can be configured to accept user input for sensor values (see [](tests/sense_actuate_0) or to generate a "random walk" of sensor values. This is controlled via the `SENSORS` build flag:

- `make SENSORS=Simulated rts` will build a simulator that generates random
  temperature/pressure data;
- `make SENSORS= rts` will build a simulator that allows the user to provide
  sensor values (`V #I #C #V`) sets channel `#C` of division `#I` to `#V`

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

## Verification with Frama-c 

ACSL contracts are provided for the components implemented under `generated` and
`handwritten` and their callers. To verify that implementations satisfy their contracts, run

`make -f frama_c.mk`

## Concurrency

The RTS implementation is a concurrent system comprising two instrumentation +
actuation logic modules plus a core logic controller.

Consulting the SysMLv2 architecture, the principal ways in which processes
communicate is via input and output values (e.g. passing trip signal values from
the instrumentation divisions to the actuation unit. Each writable memory
location has a unique writer, and system states inbetween individual writes are
consistent. Therefore, it is only necessary to guarantee that individual writes
(to shared locations) are made atomically.
