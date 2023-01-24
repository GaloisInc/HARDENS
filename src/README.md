# RTS implementation sources

This directory contains the source (both hand-written and generated, `C` and
`SystemVerilog`) for the reactor trip system:

- The root directory contains hand-written `C` sources
- [./generated_csrc](./generated_csrc) contains `C` sources generated from the `Cryptol` model
- [./generated_vsrc](./generated_vsrc) contains `SystemVerilog` sources generated from the `Cryptol` model

## Dependencies

Besides a normal `clang` toolchain, the `Makefile` targets depend on the following tools:

- `cryptol-verilogc`
  <https://gitlab-ext.galois.com/cryptol/cryptol-verilog/-/tree/signed-compare>
- `crymp` <https://gitlab-ext.galois.com/cryptol/cryptol-codegen/-/tree/hardens-tweaks> 
- `verilator` <https://www.veripool.org/verilator/> *Note* on macOS (tested on
  11.6.1) it seems there is an issue with recent versions: version 4.108 seems
  to work.
- `Cryptol` 2.11 <https://cryptol.net>
  
Verification with `frama-c` additionally requires `frama-c` version 24.0
<https://frama-c.com>.

## Implementation status

The RTS can be built for simulation on a macOS or Linux host, or (not yet
implemented) on a NERV-based SoC.

## Build parameters

- `SELF_TEST_PERIOD_SEC` controls how often to run the automatic self test, in seconds
- `PLATFORM` controls the target platform (see [below](#execution))
- `EXECUTION` controls threading (only supported on the macOS/Linux host platform) (see [below](#execution))
- `SENSORS`, `T0`, `P0`, `T_BIAS`, `P_BIAS`, `SENSOR_UPDATE_MS` control sensor modeling (see [below](#sensors))
- `T_THRESHOLD`,`P_THRESHOLD`: indicate in the UI when two sensor readings
  (temperature and pressure, respectively) differ by these thresholds (degrees F
  and 10^-5 lb/in^2, respectively)
- `SELF_TEST=Enabled` (default) builds the `rts` with a periodic self-test
  feature. `SELF_TEST=Disabled` builds the system without this feature.
  
## UI

The UI accepts commands, each of which is a single line consisting of a command
identifier plus some integer arguments.

Channels are always coded `0` for temperature, `1` for pressure, `2` for saturation.

- `A <device> <on/off>`: manually set actuation state for device `<device>` to on (`1`) or off (`0`).
- `M <div> <on/off>`: set maintenance mode for instrumentation division `<div>` to on (`1`) or off (`0`).
- `B <div> <ch> <mode>`: set division `<div>` trip for channel `<ch>` to bypass (`0`), normal (`1`), or trip (`2`).
- `S <div> <ch> <val>`: set division `<div>` setpoint for channel `<ch>` to `<val>`.
- `V <s> <ch> <val>`: simulate an input of `<val>` on the `<s>`th channel `<ch>`.
- `ES <s> <ch> <mode>`: simulate a failure in sensor `<s>` for channel `<ch>`:
  * `<mode>` = `0` disable failure
  * `<mode>` = `1` demux failure, first output
  * `<mode>` = `2` demux failure, second output
  * `<mode>` = `3` total sensor failure
  * `<mode>` = `4` nondeterministic failure in total sensor
  * `<mode>` = `5` nondeterministic failure in any demux output
- `EI <div>`: simulate a failure in instrumentation division `<div>` (`<mode>` = `0` disables, `1` enables).
- `D`: force the display to update
- `Q`: quit

## Display

The display will look something like the following:

``` sh
#I 0 (M): T[         0 B 0] P[         0 B 0] S[     -9998 B 1]
#I 1 (M): T[         0 B 1] P[         0 B 1] S[     -9998 B 1]
#I 2 (M): T[         0 B 0] P[         0 B 1] S[     -9998 B 1]
#I 3 (M): T[         0 B 0] P[         0 B 0] S[     -9998 B 1]

#A 0 [9 8]
#A 1 [0 0]

HW ACTUATORS OFF OFF





SENSORS OK
SELF TEST:     RUNNING
LAST TEST: PASS
```

The first four lines display information about each of the four instrumentation units:

- `#I <number>` identifies which unit
- `(<M or _>)` indicates the unit is in maintenance (`M`), or not (`_`).
- `<T or P or S>[ <number> <O or B or T> <byte> ]` is a channel reading:
   - `T`, `P`, `S` for temperature, pressure, and saturation margin
   - `<number>` is the sensor (or computed) reading: degrees F for `T`, 10^-5 lb/in^2 for `P` and `S`
   - `O`=normal mode, `B`=bypass, `T`=trip mode
   - The `<byte>` value's LSB indicates a signal trip if set. The MSB indicates if this is a monitored test signal.
 
The Two `#A` lines indicate the actuation unit output signals:

- `#A <number> [<byte> <byte>]` indicates the state for actuation unit
  `<number>`. The two byte values indicate the voting logic output for each
  device. The LSB indicates a vote to actuate if set, the MSB indicates if this
  is a monitored test signal.

Other output:
- `HW ACTUATORS <ON or OFF> <ON or OFF>` indicate the state of the HW actuators.
- `SENSORS <state>` indicate if sensors readings appear to diverge more than some configured threshold (see `T_THRESHOLD`,`P_THRESHOLD`).
- `SELF TEST: <state>` indicates whether or not self test is currently running
- `LAST TEST: <state>` indicates the result of the last self test.

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

The simulation build can be configured to accept user input for sensor values
(see [tests/sense_actuate_0](tests/sense_actuate_0) or to generate a "random walk" of sensor values.
This is controlled via the `SENSORS` build flag:

- `make SENSORS=Simulated rts` will build a simulator that generates random
  temperature/pressure data;

  There are a number of parameters that can control this simulation that are
  documented in the `Makefile`:
  
  - `T0`,`P0`: initial temperature and pressure readings
  - `T_BIAS`,`P_BIAS`: bias the direction of the random walk
  - `SENSOR_UPDATE_MS`: period in ms of sensor value updates

- `make SENSORS= rts` will build a simulator that allows the user to provide
  sensor values (`V #I #C #V`) sets channel `#C` of division `#I` to `#V`

- `make SENSORS=Simulated rts` will build a simulator that generates
  random temperature/pressure data;
- `make SENSORS=rts` will build a simulator that allows the user to
  provide sensor values (`V #I #C #V`) sets channel `#C` of division
  `#I` to `#V`

An example of how to script the system is given in
[tests/sense_actuate_0](tests/sense_actuate_0); you can execute

``` sh
cat tests/sense_actuate_0 | ./rts.posix
```

to run the script.

### Notes and Current Limitations

- The build system does not yet support mixing implementations of
  different components.

## Building

Run `make rts` to generate an executable simulator. To regenerate
`SystemVerilog` or `C` functions after an update to the Cryptol model,
you can run `REGEN_SOURCES=1 make <target>`; by default, the
checked-in existing generated code will be used.

## Verification with Frama-C

ACSL contracts are provided for the components implemented under
`generated` and `handwritten` and their callers. To verify that
implementations satisfy their contracts, run

`make -f frama_c.mk`

## Concurrency

The RTS implementation is a concurrent system comprising two
instrumentation + actuation logic modules plus a core logic
controller.

Consulting the SysMLv2 architecture, the principal ways in which
processes communicate is via input and output values (e.g., passing
trip signal values from the instrumentation divisions to the actuation
unit. Each writable memory location has a unique writer, and system
states inbetween individual writes are consistent. Therefore, it is
only necessary to guarantee that individual writes (to shared
locations) are made atomically.

## License

   Copyright 2021, 2022, 2023 Galois, Inc.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
