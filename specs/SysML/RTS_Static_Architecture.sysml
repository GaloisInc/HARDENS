/**
 * This RTS architecture specification includes all of the core
 * concepts inherent to NPP Instrumentation and Control systems.
 * A system architecture specification often includes a software,
 * hardware, network, and data architecture specifications.
 */
package id Architecture 'RTS Architecture' {
  //import RTS::*;
  //import 'Project Glossary'::*;
  //import Artifacts::*;
  //import 'RTS Hardware Artifacts'::*;

  part def Base_RTS_System_Architecture_Context {
    // overall RTS architecture shape from
  }

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
        attribute sensorAddress : ScalarValues::Integer;
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

    /** A generic pressure sensor. */
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
        out actuate: ScalarValues::Boolean;
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
        connect pressureDemux1.output1 to instrumentationUnit3.pressureInput;
        connect pressureDemux1.output2 to instrumentationUnit4.pressureInput;
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
