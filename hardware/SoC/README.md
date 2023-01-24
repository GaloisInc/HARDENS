# BSV SoC Wrapper for the NERV RISC-V CPU

## Version: 2022-01-07  13:38:00 EST
## Author: Rishiyur Nikhil

## Overview

Ref. "NERV" ("Naive Educational RISC-V Processor") found at:

    https://github.com/YosysHQ/nerv

This repo shows how to instantiate the CPU (in SystemVerilog file
`nerv.sv`) into a BSV harness ("SoC"), and how to build and run it
using Verilator.

Our BSV module hierarchy is: `mkTop/` `mkNervSoC/` `mkNerv/`
`mkNerv_BVI/` `nerv`, where only the bottem (`nerv`) is in
SystemVerilog (`nerv.sv` in repo) and all the layers above are in BSV,
in directory `src_BSV/`

Module `mkNervSoC` (in file `src_BSV/NervSoC.bsv`) reproduces, in BSV,
the NERV repo's SystemVerilog file `nervsoc.sv`.

Source files are in `src_BSV/`

- `Nerv_BVI.bsv` is the "raw" import of `nerv.sv`, giving us a BSV
  module constrctor `mkNerv_BVI`.

- `Nerv.bsv` is a thin wrapper that instantiates `Nerv_BVI`, and
  collects the raw `wstrb` and `wdata` into a struct returned by a
  combined method `m_get_dmem()`, and also incorporates `dmem_valid` as
  an implicit method condition.

- `NervSoC.bsv` is patterned after the original `nervsoc.sv`,
  instantiating `Nerv.bsv`.

- `Top.bsv` is a testbench that instantiates `NervSoC` and just prints
  the LED values output from `NervSoc` whenever they change to the UART.

## Building it with Verilator

    $ make compile_verilog

will invoke `bsc` (the open-source Bluespec compiler) on the
previously summarized BSV code to generate Verilog in a new `verilog/`
directory, resulting in `mkNervSoC.v`, `mkkNerv.v`, and `mkTop.v`.

    $ make link_verilator

will use Verilator to compile and link the above Verilog files
together with `nerv.sv` from the NERV repo, into a simulation
executable `exe_verilator`.  Please see the `Makefile` for the
detailed steps.

## Preparing a RISC-V program to run on the simulator

Objective: a memhex32 file `imem_contents.memhex32`, to be loaded into
NERV'S instruction memory.

The original NERV repo has a directory `examples/icebreaker/` that
contains a small example program (`firmware.c` and `firmware.s`) that
'blinks the LEDs' in the NERV system.

The directory 'Tests/icebreaker/' is a copy of that directory, plus a
few new files:

 - `firmware.elf`
 - `firmware.dump`
 - `firmware.memhex32`

`firmware.elf` is the compiled ELF file for `firmware.c` and `firmware.s`.

We can recreate this from `firmware.c` and `firmware.s` with the
following command (we need to have a RISC-V gcc compiler in our path):
```
    riscv64-unknown-elf-gcc -march=rv32i -mabi=ilp32 -Os -Wall -Wextra \
        -Wl,-Bstatic,-T,sections.lds,--strip-debug -ffreestanding -nostdlib \
        -o firmware.elf firmware.s firmware.c
```

`firmware.dump` is a disassembly of the ELF file.  We can recreate it as follows:
```
    riscv64-unknown-elf-objdump  --disassemble-all --disassemble-zeroes \
            --section=.text --section=.text.startup --section=.text.init --section=.data \
            firmware.elf | tee firmware.dump
```

`firmware.memhex32` is a memhex file of 32-bit words representing the
contents of `firmware.elf`.  We will need an ELF-to-memhex32 conversion
program for this (many are available on the Internet).

Note:
  - Each entry represents a 32-bit word (not an 8-bit byte)
  - It should start at address 0 (which is the default without any
    '@' addr line)
  - In case the memhex32 file has address lines they should be 32-bit
    word addresses (not byte addresses).
  - IMPORTANT: It should end with an entry for the last word-address
    (otherwise Verilator will complain about an incomplete memhex32 file):
```
        @3FF
        0
```

    In NERV, memory word addresses go from 0 to 1023 (0x0 to 0x3FF).

## Running a RISC-V program on the simulator

In the top-level of the repo, create/change the file
`imem_contents.memhex32` to be a copy of our memhex32 file, or a
symlink to it.

Out of the box, it is set up to run the `firmware.{c,s}` program:
```
    $ ls -als imem_contents.memhex32 
    0 lrwxrwxrwx 1 nikhil nikhil 34 Jan  7 12:57 imem_contents.memhex32 -> Tests/icebreaker/firmware.memhex32

Run it:
    $ ./exe_Verilator
    LEDs: 10101010101010101010101010101010
    LEDs: 00000000000000000000000000000000
    LEDs: 00000000000000000000000000000001
    LEDs: 00000000000000000000000000000010
    LEDs: 00000000000000000000000000000011
    LEDs: 00000000000000000000000000000100
    LEDs: 00000000000000000000000000000101
    ...
```

A transcript of about the first 100 lines is found in
`transcript_exe_Verilator`.

## Status as of 6/6/2022
* FPGA sending serial data at 76800 baud
* a simple python script will read and send data:
  ```python
  import serial
  import time
  #Serial takes two parameters: serial device and baudrate
  with serial.Serial('/dev/ttyUSB0', 76800, serial.EIGHTBITS, serial.PARITY_NONE, serial.STOPBITS_ONE) as s:
      while(1):
          s.write(bytearray([0xAA])) # TODO: replace this with real data
          print(s.readline().decode())
  ```
* tested with the demo firmware, not the real RTS one
* in Verilator read and write works, as well as simulted sensors and self-tests (simulated sensors need to be disabled for that)
* the FPGA input clock is 12MHz, the CPU clock is 1.3MHz (around 9x slowdown), this is likely related to the waits required for memory fetch (we don't use caching)
* the unfinished part on FPGA platform is:
  * serial input
  * i2c sensor communication
  * wiring of sensors, actuators and such
* the RTS for non-posix target is currently single core, which causes issues with reading serial input (we don't have interrupts on Nerv). The way to mitigate this is to move to dual-CPU configuration, where one CPU with relatively large memory will service user input/ouput (requires string parsing and manipulation libraries, hence the larger memory), and the other CPU or CPUs that implement the instrumentation/voting logic (the don't need any print functions, so the code size is rather small)

## License

   Copyright 2021, 2022, 2023 Galois, Inc.
   Copyright 2022 Bluespec, Inc.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
