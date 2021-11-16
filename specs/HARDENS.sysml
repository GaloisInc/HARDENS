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

package id Architecture 'RTS Architecture' {
  //import RTS::*;
  //import 'Project Glossary'::*;
  //import Artifacts::*;
  //import 'RTS Hardware Artifacts'::*;

  /** Note that this is the *systems* architecture, which is different
      than our software, hardware, or data architectures. */
  package id RTS_System_Arch 'RTS System Architecture' {

    package TempSensor {
      import ISQThermodynamics::TemperatureValue;

      /** Generic temperature port */
      port def TemperatureOutPort {
          out temp : TemperatureValue;
      }

      /** A sensor that is capable of measuring the temperature of its environment. */
      part def 'Temperature Sensor' {
        /** What is your temperature reading in Celsius (C)? */
        attribute currentTemp: TemperatureValue;
        port tempOut: TemperatureOutPort;
      }
    }

    package PressureSensor {
      import ISQMechanics::PressureValue;

      /** Generic pressure port */
      port def PressureOutPort {
          out pressure : PressureValue;
      }

      /** A sensor that is capable of measuring the air pressure of its environment. */
      part def 'Pressure Sensor' {
        /** What is your pressure reading in Pascal (P)? */
        attribute currentPressure: PressureValue;
        port pressureOut: PressureOutPort;
      }
    }

    package Instrumentation {
      import ScalarValues::Real;
      import ScalarValues::Boolean;
      import TempSensor::*;
      import PressureSensor::*;

      // TODO: specialize? Such as PressureTripPort etc.
      port def TripPort {
        out trip : Boolean;
      }

      part def InstrumentationUnit {
        // setpoints
        attribute tempSetpoint : TemperatureValue;
        attribute pressureSetpoint : PressureValue;
        attribute saturationLimit : Real;

        // mode selectors
        attribute maintenanceMode : Boolean;

        // Inputs
        port temperatureInput: ~TemperatureOutPort;
        port pressureInput: ~PressureOutPort;

        // Outputs
        port pressureTripOut:TripPort;
        port temperatureTripOut:TripPort;
        port saturationTripOut:TripPort;

        import EventControl::ControlPort;
        port controlInput:ControlPort;
      }
    }

    package Actuation {
      import Instrumentation::*;

      port def ActuationPort {
        out actuate: Boolean;
      }

      part def CoincidenceLogic {
        port channel1: ~TripPort;
        port channel2: ~TripPort;
        port actuate: ActuationPort;
      }
      part def OrLogic {
        port channel1: ~TripPort;
        port channel2: ~TripPort;
        port actuate: ActuationPort;
      }

     part def ActuationUnit {
       part tempLogic : CoincidenceLogic;
       part pressureLogic : CoincidenceLogic;
       part saturationLogic : OrLogic;

       import EventControl::ControlPort;
       port controlInput:ControlPort;
      }
      part def Actuator {
         port input: ActuationPort;
       }
    }

    package EventControl {
      enum def Mode {
        AUTO;
        MANUAL;
        MAINTENANCE;
      }

      port def ControlPort {
        out modeSelect: Mode;
        // NOTE: specify which setpoint? Temp/Pressure/Saturation?
        // Maybe redefine later
        out setpointSelect: ScalarValues::Real;
        out tripOn: ScalarValues::Boolean;
      }

      part def ControlUnit {
        port output: ~ControlPort;
      }
    }

    part RTS {
      import EventControl::*;
      part eventControl : ControlUnit;

      import Instrumentation::*;
      part instrumentationAndSensing {
        part pressureSensor1 : PressureSensor::'Pressure Sensor';
        part tempSensor1 : TempSensor::'Temperature Sensor';
        part instrumentationUnit1 : InstrumentationUnit;

        connect tempSensor1.tempOut to instrumentationUnit1.temperatureInput;
        connect pressureSensor1.pressureOut to instrumentationUnit1.pressureInput;
      }


      import Actuation::*;
      part actuation {
        part actuationUnit1: ActuationUnit;
        part actuator1 : Actuator;

        // connect actuators
        connect actuationUnit1.saturationLogic.actuate to actuator1.input;
      }

      // connect UI
      connect eventControl.output to instrumentationAndSensing.instrumentationUnit1.controlInput;
      connect eventControl.output to actuation.actuationUnit1.controlInput;

      // connect trip channels
      connect instrumentationAndSensing.instrumentationUnit1.pressureTripOut to actuation.actuationUnit1.pressureLogic.channel1;
      connect instrumentationAndSensing.instrumentationUnit1.temperatureTripOut to actuation.actuationUnit1.tempLogic.channel1;
      connect instrumentationAndSensing.instrumentationUnit1.saturationTripOut to actuation.actuationUnit1.saturationLogic.channel1;



    }
  } // package id RTS_System_Arch 'RTS System Architecture'
} // package id Architecture 'RTS Architecture'

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

/** The physical hardware components that are a part of the HARDENS RTS
    demonstrator. */
package 'RTS Hardware Artifacts' {
  import 'Project Glossary'::*;
  import Architecture::RTS_System_Arch::Hardware::*;
  import ScalarValues::*;

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

///** The physical architecture of the HARDENS RTS demonstrator. */
//package 'Physical Architecture' {
//  import 'Project Glossary'::*;
//  import 'RTS Hardware Artifacts'::*;
//
//  /** A PCB developer board used to prototype hardware. */
//  part 'HARDENS Demonstrator Board' : DevBoard;
//  /** The USB cable used to communicate the ASCII UI to/from the board. */
//  part id UI_C 'USB UI Cable' : 'USB Cable';
//  /** The USB cable used to program the board with a bitstream. */
//  part id Prog_C 'USB Programming Cable' : 'USB Cable';
//  /** The USB cable used to interact with the board in a debugger. */
//  part id Debug_C 'USB Debugging I/O Cable' : 'USB Cable';
//  // @trace #11 https://github.com/GaloisInc/HARDENS/issues/11
//  // @todo Add attributes for URL traceability.
//  part def id MPL3115A2 'SparkFun Altitude/Pressure Sensor Breakout' :>
//    PCB, 'Pressure Sensor';
//  // 4x https://www.sparkfun.com/products/11084
//  part def 'SparkFun MOSFET Power Control Kit' :> PCB, Power;
//  // 4x https://www.sparkfun.com/products/12959
//  part def id TMP102 'SparkFun Digital Temperature Sensor Breakout' :>
//   PCB, 'Temperature Sensor';
//  // 4x https://www.sparkfun.com/products/13314
//  part def 'Small Push-Pull Solenoid - 12VDC' :> 'Solenoid Actuator';
//  // 4x https://www.adafruit.com/product/412
//  part def '1N4001 Diode';
//  // 1x https://www.adafruit.com/product/755
//  /** The first of two redundant temperature sensors. */
//  part id TS1 'Temperature Sensor 1' : TMP102;
//  /** The second of two redundant temperature sensors. */
//  part id TS2 'Temperature Sensor 2' : TMP102;
//  /** The first of two redundant pressure sensors. */
//  part id PS1 'Pressure Sensor 1' : MPL3115A2;
//  /** The second of two redundant pressure sensors. */
//  part id PS2 'Pressure Sensor 2' : MPL3115A2;
//  /** The first of two redundant solenoid actuators. */
//  part id SA1 'Solenoid Actuator 1' : 'Small Push-Pull Solenoid - 12VDC';
//  /** The second of two redundant solenoid actuators. */
//  part id SA2 'Solenoid Actuator 2' : 'Small Push-Pull Solenoid - 12VDC';
//  // @todo kiniry Add ports for external connectors.
//
//  /** The computer used by a developer to interface with the demonstrator,
//      typically for driving the demonstrator's UI and programming and
//      debugging the board. */
//  part def 'Developer Machine':> Computer;
//
//  /** The fully assembled HARDENS demonstrator hardware with all component present. */
//  part id Demonstrator 'HARDENS Demonstrator';
//
//  connection def DevMachineToDevBoard {
//    end: Computer;
//    end: PCB;
//  }
//    connection: DevMachineToDevBoard connect 'Developer Machine' to Board;
//}
