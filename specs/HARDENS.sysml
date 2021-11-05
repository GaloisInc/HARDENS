/*
 # Reactor Trip System (RTS) High-assurance Demonstrator
 ## project: High Assurance Rigorous Digital Engineering for Nuclear Safety (HARDENS)
 ### copyright (C) 2021 Galois
 ### author: Joe Kiniry <kiniry@galois.com>

 ## Summary

 The overall shape of the Reactor Trip System (RTS) is an archetypal
 *sense-compute-actuate* architecture. Sensors are in the `Sensors`
 subsystem. They are read by the `Instrumentation` subsystem, which
 contains four separate and independent `Instrumentation`
 components. The "Compute" part of the architecture is spread across
 the `Actuation Logic` subsystem—which contains the two `Voting`
 components which perform the actuation logic itself—and the `Root`
 subsystem which contains the core computation and I/O components, and
 the two separate and independent devices that drive actuators.
 */

package id RTS 'Reactor Trip System' {
  import 'Semantic Properties'::*;
  
  package id Architecture 'RTS Architecture';
  alias Arch for Architecture;
  package id Hardware 'RTS Hardware Artifacts';
  alias HW for Hardware;
  package id Properties 'RTS Properties';
  alias Props for Properties;
  package id Characteristics 'IEEE Std 603-2018 Characteristics';
  comment TopLevelPackages about Architecture, Hardware, Properties, Characteristics
  /* These are the core top-level subsystems characterizing HARDEN work. */
}

package Architecture {
  import RTS::*;
  import 'Project Glossary'::*;
  import Artifacts::*;
  import 'RTS Hardware Artifacts'::*;

  /** Note that this is the *systems* architecture, which is different 
      than our software, hardware, or data architectures. */
  package id RTS_System_Arch 'RTS System Architecture' {
    // doc id sys_arch_doc
    package Root {
      import 'Project Glossary'::*;
      part id CFSM 'Core Finite State Machine': FSM;
      part id Programming_IO 'Programming I/O': IO;
      part id UI_IO 'UI I/O': IO;
      part id Debugging_IO 'Debugging I/O': IO;
    }
    package 'Actuation_Logic' {
      part 'Voting Logic': 'Voting'[2];
      part 'Actuator Logic': 'Actuator'[2];
    }
    /** Documentation about computation goes here. */
    package Computation {
      part def 'RISC-V CPU':> CPU, RISC_V_ISA;
      part id CPUs 'RISC-V CPUs': 'RISC-V CPU'[3];
    }
    package Hardware {
      package FPGA {
        part id DevBoard 'Lattic ECP-5 FPGA Development Board': PCB;
      }
      package Actuators {
        part 'Actuator'[2];
      }
      package Sensors {
        part TS: 'Temperature Sensor'[2];
        part PS: 'Pressure Sensor'[2];
      }
    }
    package Instrumentation {
      part 'Instrumentation'[4];
    }
  }
}

package id Artifacts 'RTS Implementation Artifacts' {
  private import ScalarValues::*;
  private import 'Project Glossary'::*;

  // @design Remove concepts in general Glossary that duplicate or
  // overlap with these concepts.  Move abstract items to Glossary.
  part def id CryptolToC 'Cryptol Software Compiler':> Compiler {
    item input: CryptolSpec redefines input;
    item output: C_Source redefines output;
  }
  part def id CryptolToSystemVerilog 'Cryptol Hardware Compiler':> Compiler {
    item input: CryptolSpec redefines input;
    item output: SystemVerilog redefines output;
  }
  part def id CPU 'COTS High-Assurance RV32I RISC-V CPU':> CPU, RISC_V_ISA;
  part def id CompCert 'CompCert Compiler':> Compiler {
    item input: C_Source redefines input;
    item output: RISCV_Binary redefines output;
  }
  part def id BSC 'Bluespec Compiler':> Compiler {
    item input: BluespecSystemVerilog redefines input;
    item output: SystemVerilog redefines output;
  }
  part def id SymbiFlow 'SymbiFlow Synthesizer' :> Synthesizer {
    item input: SystemVerilog redefines input;
    item output: Bitstream redefines output;
  }
  part def id RTL 'Demonstrator Verilog';
  part def 'Demonstrator Bitstream':> Bitstream;
  package id Dataflow 'Dataflow of RTS Implementation Artifacts' {
    private import 'RTS Implementation Artifacts'::*;
    
    part def 'HARDENS Cryptol System Specification':> CryptolSpec {
     // :>> literate = true;
    }
    // bind 'HARDENS Cryptol System Specification'.output = CryptolToC.input;
  }
}

/** The physical hardware components that are a part of the HARDENS RTS
    demonstrator. */
package 'RTS Hardware Artifacts' {
  import 'Project Glossary'::*;
  import Architecture::RTS_System_Arch::Hardware::*;
  import ScalarValues::*;

  part def id DevBoard 'FGPA Dev Board':> PCB {
    part id J9_J26 'SERDES Test SMA Connector'[16];
    part id J38 'Parallel Config Header';
    part id J39_J40 'Versa Expansion Connector'[2];
    part id U4 'SPI Flag Configuration Memory';
    part id SW1 'CFG Switch';
    part id SW5 'Input Switch';
    part id D5_D12 'Output LED'[8];
    part id SW2_SW4 'Input Push Button'[3];
    part id J37 '12 V DC Power Input';
    part id J5_J8_J32_J33 'GPIO Headers'[4];
    part id J31 'PMOD/GPIO Header';
    part id J30 'Microphone Board/GPIO Header';
    part 'Prototype Area';
    part FPGA;
    part id U3 'ECP5-5G Device':> FPGA;
    part id J1 'JTAG Interface';
    part id J2 'Mini USB Programming';
    part id Board 'Lattice ECP-5 FPGA Development Board';
  }
  item def TemperatureValue:> Real;
  item def PressureValue:> Real;
  port def SensorValuePort {
    out item value;
  }
  abstract item def Sensor {
    port value: SensorValuePort;
  }
  /** A sensor that is capable of measuring the temperature of its environment. */
  part def 'Temperature Sensor':> Sensor {
    /** What is your temperature reading in Celcius (C)? */
    port temp redefines Sensor::value;
  }
  /** A sensor that is capable of measuring the air pressure of its environment. */
  part def 'Pressure Sensor':> Sensor {
    /** What is your pressure reading in Pascal (P)? */
    part pressure: PressureValue redefines Sensor::value;
  }
  enum def SolenoidState {
    OPEN;
    CLOSED;
  }
  /** A solenoid actuator capable of being in an open or closed state. */
  part def 'Solenoid Actuator':> Actuator {
    item actuator_state;
    /** Open! */
    port open;
    /** Close! */
    port close;
  }
}

/** The physical architecture of the HARDENS RTS demonstrator. */
package 'Physical Architecture' {
  import 'Project Glossary'::*;

  /** A PCB developer board used to prototype hardware. */
  part def id Board 'Dev Board':> PCB {
    /** The USB cable used to communicate the ASCII UI to/from the board. */    
    part def id UI_C 'USB UI Cable';
    /** The USB cable used to program the board with a bitstream. */
    part def id Prog_C 'USB Programming Cable';
    /** The USB cable used to interact with the board in a debugger. */
    part def id Debug_C 'USB Debugging I/O Cable';
    // * MOSFET power control kit: https://www.sparkfun.com/products/12959
    // * 12 V Latch solenoid: https://www.sparkfun.com/products/15324
    // * Pressure sensor: https://www.sparkfun.com/products/11084
    /** The first of two redundant temperature sensors. */
    part def id TS1 'Temperature Sensor 1';
    /** The second of two redundant temperature sensors. */
    part def id TS2 'Temperature Sensor 2';
    /** The first of two redundatnt pressure sensors. */
    part def id PS1 'Pressure Sensor 1';
    /** The second of two redundant pressure sensors. */
    part def id PS2 'Pressure Sensor 2';
    /** The first of two redundant solenoid actuators. */
    part def id SA1 'Solenoid Actuator 1';
    /** The second of two redundant solenoid actuators. */
    part def id SA2 'Solenoid Actuator 2';
    // @todo kiniry Add ports for external connectors.
  }
  /** The fully assembled HARDENS demonstrator hardware with all component present. */
  part def id Demonstrator 'HARDENS Demonstrator';

  /** The computer used by a developer to interface with the demonstrator,
      typically for driving the demonstrator's UI and programming and
      debugging the board. */
  part def 'Developer Machine':> Computer;

  connection def DevMachineToDevBoard {
    end: Computer;
    end: PCB;
  } 
//    connection: DevMachineToDevBoard connect 'Developer Machine' to Board;
}



