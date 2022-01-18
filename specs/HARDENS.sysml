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

package id Architecture 'RTS Architecture' {
  //import RTS::*;
  //import 'Project Glossary'::*;
  //import Artifacts::*;
  //import 'RTS Hardware Artifacts'::*;

  /** Note that this is the *systems* architecture, which is different
      than our software, hardware, or data architectures. */
  package id RTS_System_Arch 'RTS System Architecture' {

    package Sensor {
      private import Quantities::*;

      /** Generic sensor port */
      port def SensorOutPort {
          out value : ScalarQuantityValue;
      }

      /** Generic sensor */
      part def GenericSensor {
        attribute currentValue : ScalarQuantityValue;
        port output: SensorOutPort;
      }

      part def Demux {
        port input: ~SensorOutPort;
        // Using vector notation doesn't seem to work in connections
        port output1: SensorOutPort;
        port output2: SensorOutPort;
      }
    }

    package TempSensor {
      import Sensor::*;
      import ISQThermodynamics::TemperatureValue;

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

    package PressureSensor {
      import Sensor::*;
      import ISQMechanics::PressureValue;

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

    package Instrumentation {
      import ScalarValues::Real;
      import ScalarValues::Boolean;
      import TempSensor::*;
      import PressureSensor::*;

      port def TripPort {
        out trip : Boolean;
      }

      port def BypassPort {
        out trip : Boolean;
      }
      
      enum def TripMode {
      	enum Bypass;
      	enum Operate;
      	enum Manual;
      }
      
      enum def Channel {
      	enum Temperature;
      	enum Pressure;
      	enum Saturation;
      }
       
      attribute def TripModeCommand {
      	attribute mode: TripMode;
      	attribute channel: Channel;
      }
      
      port def TripModePort {
      	out mode: TripModeCommand;
      }
      
       part def PressureTable {
        	doc /* The saturation table gives us the saturation pressure margin given
        	     * the current temperature and pressure, hence the output is pressure
        	     */
        	port temperatureInput: ~TemperatureOutPort;
        	port pressureInput: ~PressureOutPort;
        	port saturationMarginOutput: PressureOutPort;
        }

      part def InstrumentationUnit {
        // setpoints
        attribute tempSetpoint : TemperatureValue;
        attribute pressureSetpoint : PressureValue;
        attribute saturationLimit : Real;

        // mode selectors
        attribute maintenanceMode : Boolean;
        attribute temperatureTripMode: TripMode;
        attribute pressureTripMode: TripMode;    
        attribute saturationTripMode: TripMode;
        

        // Inputs
        port temperatureInput: ~TemperatureOutPort;
        port pressureInput: ~PressureOutPort;
        port saturationMarginInput: ~PressureOutPort;
        port tripMode: ~TripModePort;      	        

        // Outputs
        port pressureTripOut:TripPort;
        port temperatureTripOut:TripPort;
        port saturationTripOut:TripPort;

        port setMaintenanceMode: ~EventControl::MaintenancePort;

        port newTemperatureSetpoint: ~TemperatureOutPort;
        port newPressureSetpoint: ~PressureOutPort;
        port newSaturationSetpoint : ~SensorOutPort;
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
        port channel3: ~TripPort;
        port channel4: ~TripPort;
        port actuate: ActuationPort;
      }
      part def OrLogic {
        port channel1: ~TripPort;
        port channel2: ~TripPort;
        port actuate: ActuationPort;
      }

     part def ActuationUnit {
       part temperatureLogic : CoincidenceLogic;
       part pressureLogic : CoincidenceLogic;
       part saturationLogic : CoincidenceLogic;

       part tempPressureTripOut: OrLogic;

       connect temperatureLogic.actuate to tempPressureTripOut.channel1;
       connect pressureLogic.actuate to tempPressureTripOut.channel2;
      }
      part def Actuator {
         // Actuate if either of these are true
         port input: ActuationPort;
         port manualActuatorInput: ~ActuationPort;
       }
    }

    package EventControl {
	  import ScalarValues::Boolean;
	  
      port def MaintenancePort {
        out maintenance: Boolean;
      }

      part def ControlUnit {
        // Maintenance mode select x 4 instrumentation units
        port maintenanceMode: MaintenancePort[4];
        // Trip mode select x 4 instrumentation units
        port tripMode: Instrumentation::TripModePort[4];
        // New setpoints x 4 instrumentation units
        port newPressureSetpoint: PressureSensor::PressureOutPort[4];
        port newTemperatureSetpoint: TempSensor::TemperatureOutPort[4];
        port newSaturationSetpoint: PressureSensor::PressureOutPort[4];
        // Toggle actuator x2 actuators
        port manualActuatorInput: Actuation::ActuationPort[2];
      }
    }

    part RTS {
      part eventControl : EventControl::ControlUnit;

      import Instrumentation::*;
      part instrumentationAndSensing {
        part pressureSensor1 : PressureSensor::'Pressure Sensor';
        part pressureSensor2 : PressureSensor::'Pressure Sensor';

        part tempSensor1 : TempSensor::'Temperature Sensor';
        part tempSensor2 : TempSensor::'Temperature Sensor';

        part instrumentationUnit1 : InstrumentationUnit;
        part instrumentationUnit2 : InstrumentationUnit;
        part instrumentationUnit3 : InstrumentationUnit;
        part instrumentationUnit4 : InstrumentationUnit;
        
        part table1 : PressureTable;
        part table2 : PressureTable;
        part table3 : PressureTable;
        part table4 : PressureTable;
        
        part tempDemux1 : TempSensor::Demux;
        part tempDemux2 : TempSensor::Demux;

        part pressureDemux1 : PressureSensor::Demux;
        part pressureDemux2 : PressureSensor::Demux;

        // Temp sensor 1
        connect tempSensor1.output to tempDemux1.input;
        connect tempDemux1.output1 to instrumentationUnit1.temperatureInput;
        connect tempDemux1.output2 to instrumentationUnit2.temperatureInput;

        // Temp sensor 2
        connect tempSensor2.output to tempDemux2.input;
        connect tempDemux2.output1 to instrumentationUnit3.temperatureInput;
        connect tempDemux2.output2 to instrumentationUnit4.temperatureInput;

        // Pressure sensor 1
        connect pressureSensor1.output to pressureDemux1.input;
        connect pressureDemux1.output1 to instrumentationUnit1.pressureInput;
        connect pressureDemux1.output2 to instrumentationUnit2.pressureInput;

        // Pressure sensor 2
        connect pressureSensor2.output to pressureDemux2.input;
        connect pressureDemux2.output1 to instrumentationUnit3.pressureInput;
        connect pressureDemux2.output2 to instrumentationUnit4.pressureInput;
        
        // Saturation Margin Calculation
        connect pressureDemux1.output1 to table1.pressureInput;
        connect tempDemux1.output1 to table1.temperatureInput;
        connect table1.saturationMarginOutput to instrumentationUnit1.saturationMarginInput;
        
        connect pressureDemux1.output2 to table2.pressureInput;
        connect tempDemux1.output2 to table2.temperatureInput;
        connect table2.saturationMarginOutput to instrumentationUnit2.saturationMarginInput;
        
        connect pressureDemux2.output1 to table3.pressureInput;
        connect tempDemux2.output1 to table3.temperatureInput;
        connect table3.saturationMarginOutput to instrumentationUnit3.saturationMarginInput;
        
        connect pressureDemux2.output2 to table4.pressureInput;
        connect tempDemux2.output2 to table4.temperatureInput;
        connect table4.saturationMarginOutput to instrumentationUnit4.saturationMarginInput;
      }


      import Actuation::*;
      part actuation {
        part actuationUnit1: ActuationUnit;
        part actuationUnit2: ActuationUnit;

        part actuator1 : Actuator;
        part actuator2 : Actuator;

        part actuateActuator1: OrLogic;
        part actuateActuator2: OrLogic;

        // connect actuators
        // Actuator 1 - temp or pressure trip
        connect actuationUnit1.tempPressureTripOut.actuate to actuateActuator1.channel1;
        connect actuationUnit2.tempPressureTripOut.actuate to actuateActuator1.channel2;
        connect actuateActuator1.actuate to actuator1.input;

        // Actuator 2 - Saturation
        connect actuationUnit1.saturationLogic.actuate to actuateActuator2.channel1;
        connect actuationUnit2.saturationLogic.actuate to actuateActuator2.channel2;
        connect actuateActuator2.actuate to actuator2.input;
      }

      // connect Control units
      // Actuators manual override
      connect eventControl.manualActuatorInput[1] to actuation.actuator1.manualActuatorInput;
      connect eventControl.manualActuatorInput[2] to actuation.actuator2.manualActuatorInput;

      // Instrumentation mode select
      connect eventControl.maintenanceMode[1] to instrumentationAndSensing.instrumentationUnit1.setMaintenanceMode;
      connect eventControl.maintenanceMode[2] to instrumentationAndSensing.instrumentationUnit2.setMaintenanceMode;
      connect eventControl.maintenanceMode[3] to instrumentationAndSensing.instrumentationUnit3.setMaintenanceMode;
      connect eventControl.maintenanceMode[4] to instrumentationAndSensing.instrumentationUnit4.setMaintenanceMode;


      // Instrumentation pressure setpoint
      connect eventControl.newPressureSetpoint[1] to instrumentationAndSensing.instrumentationUnit1.newPressureSetpoint;
      connect eventControl.newPressureSetpoint[2] to instrumentationAndSensing.instrumentationUnit2.newPressureSetpoint;
      connect eventControl.newPressureSetpoint[3] to instrumentationAndSensing.instrumentationUnit3.newPressureSetpoint;
      connect eventControl.newPressureSetpoint[4] to instrumentationAndSensing.instrumentationUnit4.newPressureSetpoint;

      // Instrumentation temperature setpoint
      connect eventControl.newTemperatureSetpoint[1] to instrumentationAndSensing.instrumentationUnit1.newTemperatureSetpoint;
      connect eventControl.newTemperatureSetpoint[2] to instrumentationAndSensing.instrumentationUnit2.newTemperatureSetpoint;
      connect eventControl.newTemperatureSetpoint[3] to instrumentationAndSensing.instrumentationUnit3.newTemperatureSetpoint;
      connect eventControl.newTemperatureSetpoint[4] to instrumentationAndSensing.instrumentationUnit4.newTemperatureSetpoint;

      // Instrumentation saturation setpoint
      connect eventControl.newSaturationSetpoint[1] to instrumentationAndSensing.instrumentationUnit1.newSaturationSetpoint;
      connect eventControl.newSaturationSetpoint[2] to instrumentationAndSensing.instrumentationUnit2.newSaturationSetpoint;
      connect eventControl.newSaturationSetpoint[3] to instrumentationAndSensing.instrumentationUnit3.newSaturationSetpoint;
      connect eventControl.newSaturationSetpoint[4] to instrumentationAndSensing.instrumentationUnit4.newSaturationSetpoint;

      // Instrumentation trip mode
      // Bypass temperature
      connect eventControl.tripMode[1] to instrumentationAndSensing.instrumentationUnit1.tripMode;
      connect eventControl.tripMode[2] to instrumentationAndSensing.instrumentationUnit2.tripMode;
      connect eventControl.tripMode[3] to instrumentationAndSensing.instrumentationUnit3.tripMode;
      connect eventControl.tripMode[4] to instrumentationAndSensing.instrumentationUnit4.tripMode;

      // Trip on pressure above the setpoint
      // Actuation unit 1
      connect instrumentationAndSensing.instrumentationUnit1.pressureTripOut to actuation.actuationUnit1.pressureLogic.channel1;
      connect instrumentationAndSensing.instrumentationUnit2.pressureTripOut to actuation.actuationUnit1.pressureLogic.channel2;
      connect instrumentationAndSensing.instrumentationUnit3.pressureTripOut to actuation.actuationUnit1.pressureLogic.channel3;
      connect instrumentationAndSensing.instrumentationUnit4.pressureTripOut to actuation.actuationUnit1.pressureLogic.channel4;
      // Actuation unit 2
      connect instrumentationAndSensing.instrumentationUnit1.pressureTripOut to actuation.actuationUnit2.pressureLogic.channel1;
      connect instrumentationAndSensing.instrumentationUnit2.pressureTripOut to actuation.actuationUnit2.pressureLogic.channel2;
      connect instrumentationAndSensing.instrumentationUnit3.pressureTripOut to actuation.actuationUnit2.pressureLogic.channel3;
      connect instrumentationAndSensing.instrumentationUnit4.pressureTripOut to actuation.actuationUnit2.pressureLogic.channel4;

      // Trip on temperature above the setpoint
      // Actuation unit 1
      connect instrumentationAndSensing.instrumentationUnit1.temperatureTripOut to actuation.actuationUnit1.temperatureLogic.channel1;
      connect instrumentationAndSensing.instrumentationUnit2.temperatureTripOut to actuation.actuationUnit1.temperatureLogic.channel2;
      connect instrumentationAndSensing.instrumentationUnit3.temperatureTripOut to actuation.actuationUnit1.temperatureLogic.channel3;
      connect instrumentationAndSensing.instrumentationUnit4.temperatureTripOut to actuation.actuationUnit1.temperatureLogic.channel4;
      // Actuation unit 2
      connect instrumentationAndSensing.instrumentationUnit1.temperatureTripOut to actuation.actuationUnit2.temperatureLogic.channel1;
      connect instrumentationAndSensing.instrumentationUnit2.temperatureTripOut to actuation.actuationUnit2.temperatureLogic.channel2;
      connect instrumentationAndSensing.instrumentationUnit3.temperatureTripOut to actuation.actuationUnit2.temperatureLogic.channel3;
      connect instrumentationAndSensing.instrumentationUnit4.temperatureTripOut to actuation.actuationUnit2.temperatureLogic.channel4;

      // Trip on saturation above the setpoint
      // Actuation unit 1
      connect instrumentationAndSensing.instrumentationUnit1.saturationTripOut to actuation.actuationUnit1.saturationLogic.channel1;
      connect instrumentationAndSensing.instrumentationUnit2.saturationTripOut to actuation.actuationUnit1.saturationLogic.channel2;
      connect instrumentationAndSensing.instrumentationUnit3.saturationTripOut to actuation.actuationUnit1.saturationLogic.channel3;
      connect instrumentationAndSensing.instrumentationUnit4.saturationTripOut to actuation.actuationUnit1.saturationLogic.channel4;
      // Actuation unit 2
      connect instrumentationAndSensing.instrumentationUnit1.saturationTripOut to actuation.actuationUnit2.saturationLogic.channel1;
      connect instrumentationAndSensing.instrumentationUnit2.saturationTripOut to actuation.actuationUnit2.saturationLogic.channel2;
      connect instrumentationAndSensing.instrumentationUnit3.saturationTripOut to actuation.actuationUnit2.saturationLogic.channel3;
      connect instrumentationAndSensing.instrumentationUnit4.saturationTripOut to actuation.actuationUnit2.saturationLogic.channel4;


    }
  } // package id RTS_System_Arch 'RTS System Architecture'
} // package id Architecture 'RTS Architecture'

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
  //import Architecture::RTS_System_Arch::Hardware::*;
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
    import 'Project Glossary'::*;
    
    requirement def 'Project Requirements' {
      subject 'NRC staff' : NRC;
    }
    requirement 'NRC Understanding' : 'Project Requirements';
    requirement 'Identify Regulatory Gaps' : 'Project Requirements';
    requirement Demonstrate : 'Project Requirements';
    requirement 'Demonstrator Parts' : 'Project Requirements';
    requirement 'Demonstrator Groundwork' : 'Project Requirements';
 }
 package id Characteristics 'NRC Characteristics' {
   import 'Project Glossary'::*;
   requirement def 'NRC Characteristic' {
     subject regulation: 'NRC Certification Regulations';
   }
   requirement 'Requirements Consistency' : 'NRC Characteristic';
   requirement 'Requirements Colloquial Completeness' : 'NRC Characteristic';
   requirement 'Requirements Formal Completeness' : 'NRC Characteristic';
   requirement 'Instrumentation Independence' : 'NRC Characteristic';
   requirement 'Channel Independence' : 'NRC Characteristic';
   requirement 'Actuation Independence' : 'NRC Characteristic';
   requirement 'Actuation Correctness' : 'NRC Characteristic';
   requirement 'Self-Test/Trip Independence' : 'NRC Characteristic';
 }
 // Note that formal requirements expressed externally must be traceable
 // to this system model, but need not be repeated in whole here.  Model
 // elements that are expressed in both the SysML and FRET models must
 // be in a refinement relationship with each other (e.g,, in this case study,
 // SysML ⊑ FRET.
 package 'Formal Requirements' {
   import 'Project Glossary'::*;
   requirement def id FRET 'FRET Requirements' {
     doc /* RTS requirements formalized in the FRET tool. */     
   }
   // @todo kiniry Complete remaining FRET requirements.
   requirement ACTUATION_ACTUATOR_0 : FRET;
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

/**
 * The set of all atomic external or internal actions that the RTS
 * system can take.  Note that every scenario must be describable by
 * a sequence of actions. 
 */
package id Actions 'RTS Actions' {
  package id Internal 'RTS Internal Actions' {
    action def id IA 'Intenral Action' {
      doc /* Actions internal to the RTS */
    }
    action id Trip 'Signal Trip' : IA {
    	in item division;
    	in item channel;
    }
    action id Vote 'Vote on Like Trips using Two-out-of-four Coincidence' : IA {
    	in item divisions[2];
    	in item channel;
    }
    action id A 'Automatically Actuate Device' : IA {
    	in item device;
    }
    action id T 'Self-test of Safety Signal Path' : IA;
  } 
  package id External 'RTS External Actions' {
    package 'UI Actions' {
      action def id UIA 'UI Action' {
        doc /* Actions exhibited by the RTS UI, either inbound or outbound. */
      }
      // @design kiniry These should both be specializations of UIA, but I
      // don't know how to write that in SysML yet.
      action def id UI_IA 'UI Input Action';
      action def id UI_OA 'UI Output Action';
      
      // Input actions.
      // @todo kiniry Add features to correspond to UI parameters.
      action id A Actuate : UI_IA {
        in item actuator;
        in item on_off;
      }
      action id M 'Set Maintenance Mode' :  UI_IA {
        in item division;
        in item on_off;
      }
      action id B 'Set Mode' : UI_IA {
        in item division;
        in item trip_mode; 
      } 
      action id S 'Set Setpoint' : UI_IA {
        in item division;
        in item channel;
        in item value;
      }
      action id V 'Sensor Value' : UI_IA {
      	doc /* Simulate a sensor reading */
      	in item division;
      	in item channel;
      	in item value;
      }
      action id Q 'Quit' : UI_IA;
      
      // Output actions.
      action id 'Display Pressure' : UI_OA;
      action id 'Display Temperature' : UI_OA;
      action id 'Display Saturation Margin': UI_OA;
      action id 'Display Trip Ouput Signal State': UI_OA;
      action id 'Display Indication Of Channel in Bypass': UI_OA;
      action id 'Display Actuation State': UI_OA;
    }
  }
} 

/**
 * The set of all scenarios that describe interesting end-to-end executions
 * of the RTS system.  The full set of scenarios must include all normal
 * behavior (online and during sefl-test) and exceptional behavior.  
 */
package id Scenarios 'RTS Scenarios' {
  package id Normal 'RTS Normal Behavior Scenarios' {
    import 'RTS Architecture'::'RTS System Architecture'::RTS;
    
    item def 'RTS User';
    use case def id NB 'Normal Behavior' {
      subject RTS;
      actor user : 'RTS User';
      objective {
        doc /* @see test_scenarios.lando */
      }
    }
    // @design kiniry Actually, ST should specialize NB.  I don't know how
    // to express that in SysML yet.
    use case def id ST 'Normal Behavior Under Self-Test' {
        subject RTS;
        actor tester : 'RTS User';
    }
    package 'Self-test Scenarios' {
      import Normal::ST;
      use case '1a - Trip on Mock High Pressure Reading from that Pressure Sensor' : NB;
      use case '1b - Trip on Environmental High Pressure Reading from that Pressure Sensor' : NB;
      use case '2a - Trip on Mock High Temperature Reading from that Temperature Sensor' : NB;
      use case '2a - Trip on Environmental High Temperature Reading from that Temperature Sensor' : NB;
      use case '3a - Trip on Mock Low Saturation Margin' : NB;
      use case '3a - Trip on Environmental Low Saturation Margin' : NB;
      use case '4 - Vote on Every Possible Like Trip' : NB;
      use case '5a - Automatically Actuate All Mock Devices in Sequence' : NB;
      use case '5b - Automatically Actuate All Mock Devices in Sequence' : NB;
      use case '6 - Manually Actuate Each Device in Sequence' : NB;
      use case '7a - Select Maintenance Operating Mode for each Division' : NB;
      use case '7b - Select Normal Operating Mode for each Division' : NB;
      use case '8 - Perform Each Kind of Setpoint Adjustment' : NB;
      use case '9 - Configure Bypass of Each Instrument Channel in Sequence' : NB;
      use case '10 - Configure Active Trip Output State of Each Instrument Channel in Sequence' : NB;
      use case '11 - Display Pressure, Temperature, and Saturation Margin' : NB;
      use case '13 - Display Indication of Every Channel in Bypass in Sequence' : NB;
      use case '14 - Demonstrate Periodic Continual Self-test of Safety Signal Path' : NB;
      use case 'Full Self-Test' : NB;
    }
    package 'RTS Scenarios' {
      // @todo Still need to enumerate these.      
    }
  } 
  package id Exceptional 'RTS Exceptional Behavior Scenarios' {
    use case def id EB 'Exceptional Behavior' {
      subject RTS;
      objective {
        doc /* @see test_scenarios.lando */
      }
    }
    use case '1a - Cause Actuator 1 to Fail' : EB;
    use case '1b - Cause Actuator 2 to Fail' : EB;
    use case '1c - Non-determinisitically Cause an Actuator to Eventually Fail' : EB;
    use case '2a - Cause Temperature Sensor 1 to Fail' : EB;
    use case '2b - Cause Temperature Sensor 2 to Fail' : EB;
    use case '2c - Non-deterministically Cause a Temperature Sensor to Eventually Fail' : EB;
    use case '3a - Cause Pressure Sensor 1 to Fail' : EB;
    use case '3b - Cause Pressure Sensor 2 to Fail' : EB;
    use case '3c - Non-deterministically Cause a Pressure Sensor to Eventually Fail' : EB;
    use case '4a - Cause Instrumentation Unit 1 to Fail' : EB;
    use case '4b - Cause Instrumentation Unit 2 to Fail' : EB;
    use case '4c - Cause Instrumentation Unit 3 to Fail' : EB;
    use case '4d - Cause Instrumentation Unit 4 to Fail' : EB;
    use case '4e - Non-Deterministically Cause Instrumentation Unit to Eventually Fail' : EB;
    // @review kiniry I actually don't know if we are fault tolerant to' : EB;
    // failure in these components.  Please review @abakst.
    use case '5a - Cause Temperature Demultiplexor 1 to Fail' : EB;
    use case '5b - Cause Temperature Demultiplexor 2 to Fail' : EB;
    use case '5b - Cause a Temperature Demultiplexor to Eventualy Fail' : EB;
  }
}

)
