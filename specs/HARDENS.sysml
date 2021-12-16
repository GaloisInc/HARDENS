/*
 # Reactor Trip System (RTS) High-assurance Demonstrator
 ## project: High Assurance Rigorous Digital Engineering for Nuclear Safety (HARDENS)
 ### copyright (C) 2021 Galois
 ### author: Joe Kiniry <kiniry@galois.com>
*/

/**
 * The overall shape of the Reactor Trip System (RTS) is an archetypal
 * *sense-compute-actuate* architecture. Sensors are in the `Sensors`
 * subsystem. They are read by the `Instrumentation` subsystem, which
 * contains four separate and independent `Instrumentation`
 * components. The "Compute" part of the architecture is spread across
 * the `Actuation Logic` subsystem—which contains the two `Voting`
 * components which perform the actuation logic itself—and the `Root`
 * subsystem which contains the core computation and I/O components, and
 * the two separate and independent devices that drive actuators.
 */
package id RTS 'Reactor Trip System' {
  private import 'Semantic Properties'::*;
  
  package id Architecture 'RTS Architecture';
  alias Arch for Architecture;
  package id Hardware 'RTS Hardware Artifacts';
  alias HW for Hardware;
  package id Artifacts 'RTS Implementation Artifacts';
  package id Requirements 'RTS Requirements';
  package id Properties 'RTS Properties';
  alias Props for Properties;
  package id Characteristics 'IEEE Std 603-2018 Characteristics';
  comment TopLevelPackages about Architecture, Hardware, Properties, Characteristics
  /* These are the core top-level subsystems characterizing HARDEN work. */
}

package 'Kiniry RTS System Architecture Draft' {
  private import 'Project Glossary'::*;

  // doc id sys_arch_doc
  package Root {
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

/**
 * This RTS architecture specification includes all of the core
 * concepts inherent to NPP Instrumentation and Control systems.
 * A system architecture specification often includes a software,
 * hardware, network, and data architecture specifications.
 */
package id Architecture 'RTS Architecture' {
  private import 'Project Glossary'::*;

  /**
   * Note that this is the *systems* architecture, which is different
   * than our software, hardware, or data architectures.
   */
  package id RTS_System_Arch 'RTS System Architecture' {

    package Sensor {
      private import Quantities::*;

      /** Generic sensor port */
      port def SensorOutPort {
          out value : ScalarQuantityValue;
      }

      /** Generic sensor */
      part def GenericSensor :> Sensor {
        attribute currentValue : ScalarQuantityValue;
        port output: SensorOutPort;
      }

      /**
       * A demultiplexer for sending one sensor signal to multiple
       * outputs. 
       */
      part def Demux {
        port input: ~SensorOutPort;
        // Using vector notation doesn't seem to work in connections
        port output1: SensorOutPort;
        port output2: SensorOutPort;
      }
    }

    /** A generic temperature sensor. */
    package TempSensor {
      private import Sensor::*;
      private import ISQThermodynamics::TemperatureValue;

      /** Temperature port */
      port def TemperatureOutPort :> SensorOutPort {
          redefines value: TemperatureValue;
      }

      /** A sensor that is capable of measuring the temperature of its environment. */
      part def 'Temperature Sensor' :> GenericSensor {
        /** What is your temperature reading in Celsius (C)? */
        redefines currentValue: TemperatureValue;
        redefines output: TemperatureOutPort;
      }

      part def TempDemux :> Demux {
        redefines input: ~TemperatureOutPort;
        redefines output1: TemperatureOutPort;
        redefines output2: TemperatureOutPort;
      }
    }

    /** A generic pressure sensor. */
    package PressureSensor {
      private import Sensor::*;
      private import ISQMechanics::PressureValue;

      /** Pressure port */
      port def PressureOutPort :> SensorOutPort {
          redefines value: PressureValue;
      }

      /** A sensor that is capable of measuring the air pressure of its environment. */
      part def 'Pressure Sensor' :> GenericSensor {
        /** What is your pressure reading in Pascal (P)? */
        redefines currentValue: PressureValue;
        redefines output: PressureOutPort;
      }

      part def PressureDemux :> Demux {
        redefines input: ~PressureOutPort;
        redefines output1: PressureOutPort;
        redefines output2: PressureOutPort;
      }
    }

    /**
     * The Instrumentation subsystem contains all of the sensors for an 
     * NPP I&C system.
     */
    package Instrumentation {
      private import ScalarValues::Real;
      private import ScalarValues::Boolean;
      private import TempSensor::*;
      private import PressureSensor::*;

      port def TripPort {
        out trip : Boolean;
      }
      package Actuators {
        part 'Actuator'[2];
      }
      package Sensors {
        part TS: 'Temperature Sensor'[2];
        part PS: 'Pressure Sensor'[2];
      }
    }
  }
}

package id Artifacts 'RTS Implementation Artifacts' {
  private import ScalarValues::*;
  private import 'Project Glossary'::*;

  // @design Remove concepts in general Glossary that duplicate or
  // overlap with these concepts.  Move abstract items to Glossary.
  part def id CryptolToC 'Cryptol Software Compiler':> Compiler {
    ref item input: CryptolSpec redefines input;
    ref item output: C_Source redefines output;
  }
  part def id CryptolToSystemVerilog 'Cryptol Hardware Compiler':> Compiler {
    ref item input: CryptolSpec redefines input;
    ref item output: SystemVerilog redefines output;
  }
  part def id CPU 'COTS High-Assurance RV32I RISC-V CPU':> CPU, RISC_V_ISA;
  part def id CompCert 'CompCert Compiler':> Compiler {
    ref item input: C_Source redefines input;
    ref item output: RISCV_Binary redefines output;
  }
  part def id BSC 'Bluespec Compiler':> Compiler {
    ref item input: BluespecSystemVerilog redefines input;
    ref item output: SystemVerilog redefines output;
  }
  part def id SymbiFlow 'SymbiFlow Synthesizer' :> Synthesizer {
    ref item input: SystemVerilog redefines input;
    ref item output: Bitstream redefines output;
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

/**
 * The physical hardware components that are a part of the HARDENS RTS
 * demonstrator. 
 */
package 'RTS Hardware Artifacts' {
  private import 'Project Glossary'::*;
  private import 'Kiniry RTS System Architecture Draft'::*;
  private import ScalarValues::*;

  part def 'SERDES Test SMA Connector' :> Connector;
  part def 'Parallel Config Header' :> Header;
  part def 'Versa Expansion Connector' :> Connector;
  part def 'SPI Flag Configuration Memory' :> Memory;
  part def 'CFG Switch' :> Switch;
  part def 'Input Switch' :> Switch;
  part def 'Output LED' :> LED;
  part def 'Input Push Button' :> Button;
  part def '12 V DC Power Input' :> Power;
  part def 'GPIO Headers' :> Header, GPIO;
  part def 'PMOD/GPIO Header' :> Header, PMOD, GPIO;
  part def 'Microphone Board/GPIO Header' :> Header;
  part def 'ECP5-5G Device' :> FPGA;
  // @todo Ensure that JTAG is, in fact, USB.
  part def 'JTAG Interface' :> JTAG, USB;
  part def 'Mini USB Programming' :> USB;
  part def id DevBoard 'Lattice ECP-5 FPGA Development Board' :> PCB {
    part J9_J26 : 'SERDES Test SMA Connector'[16] subsets components;
    part J38 : 'Parallel Config Header' subsets components;
    part J39_J40 : 'Versa Expansion Connector'[2] subsets components;
    part U4 : 'SPI Flag Configuration Memory' subsets components;
    part SW1 : 'CFG Switch' subsets components;
    part SW5 : 'Input Switch' subsets components;
    part D5_D12 : 'Output LED'[8] subsets components;
    part SW2_SW4 : 'Input Push Button'[3] subsets components;
    part J37 : '12 V DC Power Input' subsets components;
    part J5_J8_J32_J33 : 'GPIO Headers'[4] subsets components;
    part J31 : 'PMOD/GPIO Header' subsets components;
    part J30 : 'Microphone Board/GPIO Header' subsets components;
    part 'Prototype Area';
    part U3 : 'ECP5-5G Device' subsets components;
    part J1 : 'JTAG Interface' subsets components;
    part J2 : 'Mini USB Programming' subsets components;
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
  private import 'Project Glossary'::*;
  private import 'RTS Hardware Artifacts'::*;

  /** A PCB developer board used to prototype hardware. */
  part 'HARDENS Demonstrator Board' : DevBoard;
  /** The USB cable used to communicate the ASCII UI to/from the board. */    
  part id UI_C 'USB UI Cable' : 'USB Cable';
  /** The USB cable used to program the board with a bitstream. */
  part id Prog_C 'USB Programming Cable' : 'USB Cable';
  /** The USB cable used to interact with the board in a debugger. */
  part id Debug_C 'USB Debugging I/O Cable' : 'USB Cable';
  // @trace #11 https://github.com/GaloisInc/HARDENS/issues/11
  // @todo Add attributes for URL traceability.
  part def id MPL3115A2 'SparkFun Altitude/Pressure Sensor Breakout' :> 
    PCB, 'Pressure Sensor'; 
  // 4x https://www.sparkfun.com/products/11084
  part def 'SparkFun MOSFET Power Control Kit' :> PCB, Power;
  // 4x https://www.sparkfun.com/products/12959
  part def id TMP102 'SparkFun Digital Temperature Sensor Breakout' :>
    PCB, 'Temperature Sensor'; 
  // 4x https://www.sparkfun.com/products/13314
  part def 'Small Push-Pull Solenoid - 12VDC' :> 'Solenoid Actuator'; 
  // 4x https://www.adafruit.com/product/412
  part def '1N4001 Diode';
  // 1x https://www.adafruit.com/product/755
  /** The first of two redundant temperature sensors. */
  part id TS1 'Temperature Sensor 1' : TMP102;
  /** The second of two redundant temperature sensors. */
  part id TS2 'Temperature Sensor 2' : TMP102;
  /** The first of two redundant pressure sensors. */
  part id PS1 'Pressure Sensor 1' : MPL3115A2;
  /** The second of two redundant pressure sensors. */
  part id PS2 'Pressure Sensor 2' : MPL3115A2;
  /** The first of two redundant solenoid actuators. */
  part id SA1 'Solenoid Actuator 1' : 'Small Push-Pull Solenoid - 12VDC';
  /** The second of two redundant solenoid actuators. */
  part id SA2 'Solenoid Actuator 2' : 'Small Push-Pull Solenoid - 12VDC';
  // @todo kiniry Add ports for external connectors.

  /** The computer used by a developer to interface with the demonstrator,
      typically for driving the demonstrator's UI and programming and
      debugging the board. */
  part def 'Developer Machine':> Computer;

  /** The fully assembled HARDENS demonstrator hardware with all component present. */
  part id Demonstrator 'HARDENS Demonstrator';

  connection def DevMachineToDevBoard {
    end: Computer;
    end: PCB;
  } 
//    connection: DevMachineToDevBoard connect 'Developer Machine' to Board;
}

/**
 * All requirements that the RTS system must fulfill, as driven by the
 * IEEE 603-2018 standards and the NRC RFP.
 */
package id Requirements 'RTS Requirements' {
 // Note that we do not specify documentation comments here as they
 // are specified in the Lando specification.  If we do not include
 // additional specifications here on the refinement from the higher-level
 // specification (in this case, SysML refines Lando), then the higher-level
 // specification's comments/specifications refine too (an hence are 
 // just copied verbatim).
 package id Requirements 'HARDENS Project High-level Requirements' {
   requirement def 'NRC Understanding';
   requirement def 'Identify Regulatory Gaps';
   requirement def Demonstrate;
   requirement def 'Demonstrator Parts';
   requirement 'Demonstrator Groundwork';
 }
 package id Characteristics 'NRC Characteristics' {
   requirement def 'Requirements Consistency';
   requirement def 'Requirements Colloquial Completeness';
   requirement def 'Requirements Formal Completeness';
   requirement def 'Instrumentation Independence';
   requirement def 'Channel Independence';
   requirement def 'Actuation Independence';
   requirement def 'Actuation Correctness';
   requirement def 'Self-Test/Trip Independence';
 }
}

/**
 * All correctness and security properties of the RTS system are
 * specified in this subsystem.
 */
package id Properties 'RTS Properties' {
}

/**
 * The IEEE 603-2018 requirements (known as "characteristics" in
 * the standard) which the RTS demonstrator system must fulfill.
 */
package id Characteristics 'IEEE Std 603-2018 Characteristics' {
}

