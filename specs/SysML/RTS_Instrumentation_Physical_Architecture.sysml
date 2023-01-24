/*
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
*/

/* RTS_Instrumentation_Physical_Architecture.sysml*/

/** The physical hardware components that are a part of the HARDENS RTS
    demonstrator. */
package 'RTS Instrumentation Physical Architecture' {

  package TempSensor {
    import ISQThermodynamics::TemperatureValue;

    /** Generic temperature port */
    port def TemperatureOutPort {
        out temp : TemperatureValue;
    }

    /** Temperature interface */
    interface def TemperatureInterface {
      // each sensor is connected to two instrumentation units
      end supplierPort : TemperatureOutPort;
      end consumerPort1 : ~TemperatureOutPort;
      end consumerPort2 : ~TemperatureOutPort;
    }

    /** A sensor that is capable of measuring the temperature of its environment. */
    part def 'Temperature Sensor' {
      /** What is your temperature reading in Celcius (C)? */
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

    /** Pressure sensor interface */
    interface def PressureInterface {
      // each sensor is connected to two instrumentation units
      end supplierPort : PressureOutPort;
      end consumerPort1 : ~PressureOutPort;
      end consumerPort2 : ~PressureOutPort;
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

    port def TripPort {
      out trip : Boolean;
    }

    interface def TripInterface {
      // Each trip interface has 1 trip sources, and 1 consumer
      end supplierPort : TripPort;
      end consumerPort : ~TripPort;
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
    }
    part def Actuator {
       port input: ActuationPort;
     }
    interface def OrGate {
      end inputA: ActuationPort;
      end inputB: ActuationPort;
      end output: ~ActuationPort;
    }
  }

  part RTS {
    import TempSensor::*;
    part tempSensor1 : 'Temperature Sensor';
    part tempSensor2 : 'Temperature Sensor';

    import PressureSensor::*;
    part pressureSensor1 : 'Pressure Sensor';
    part pressureSensor2 : 'Pressure Sensor';

    import Instrumentation::*;
    part InstrumentationUnit1 : InstrumentationUnit;
    part InstrumentationUnit2 : InstrumentationUnit;
    part InstrumentationUnit3 : InstrumentationUnit;
    part InstrumentationUnit4 : InstrumentationUnit;

    import Actuation::*;
    part ActuationUnit1: ActuationUnit;
    part ActuationUnit2: ActuationUnit;
    part Actuator1 : Actuator;
    part Actuator2 : Actuator;

    // connect sensors
    interface T1 : TemperatureInterface
      connect tempSensor1.tempOut to InstrumentationUnit1.temperatureInput;
      connect tempSensor1.tempOut to InstrumentationUnit2.temperatureInput;

    interface T2 : TemperatureInterface
      connect tempSensor2.tempOut to InstrumentationUnit3.temperatureInput;
      connect tempSensor2.tempOut to InstrumentationUnit4.temperatureInput;

    interface P1 : PressureInterface
      connect pressureSensor1.pressureOut to InstrumentationUnit1.pressureInput;
      connect pressureSensor1.pressureOut to InstrumentationUnit2.pressureInput;

    interface P2 : PressureInterface
      connect pressureSensor2.pressureOut to InstrumentationUnit3.pressureInput;
      connect pressureSensor2.pressureOut to InstrumentationUnit4.pressureInput;

    // connect actuation logic
    // Temperature channels
    interface TripTemp1 : TripInterface
      connect InstrumentationUnit1.temperatureTripOut to ActuationUnit1.tempLogic.channel1;
    interface TripTemp2 : TripInterface
      connect InstrumentationUnit2.temperatureTripOut to ActuationUnit1.tempLogic.channel2;
    interface TripTemp3 : TripInterface
      connect InstrumentationUnit3.temperatureTripOut to ActuationUnit2.tempLogic.channel1;
    interface TripTemp4 : TripInterface
      connect InstrumentationUnit4.temperatureTripOut to ActuationUnit2.tempLogic.channel2;
    // Pressure channels
    interface TripPressure1 : TripInterface
      connect InstrumentationUnit1.pressureTripOut to ActuationUnit1.pressureLogic.channel1;
    interface TripPressure2 : TripInterface
      connect InstrumentationUnit2.pressureTripOut to ActuationUnit1.pressureLogic.channel2;
    interface TripPressure3 : TripInterface
      connect InstrumentationUnit3.pressureTripOut to ActuationUnit2.pressureLogic.channel1;
    interface TripPressure4 : TripInterface
      connect InstrumentationUnit4.pressureTripOut to ActuationUnit2.pressureLogic.channel2;
    // Saturation channels
    interface TripSaturation1 : TripInterface
      connect InstrumentationUnit1.saturationTripOut to ActuationUnit1.saturationLogic.channel1;
    interface TripSaturation2 : TripInterface
      connect InstrumentationUnit2.saturationTripOut to ActuationUnit1.saturationLogic.channel2;
    interface TripSaturation3 : TripInterface
      connect InstrumentationUnit3.saturationTripOut to ActuationUnit2.saturationLogic.channel1;
    interface TripSaturation4 : TripInterface
      connect InstrumentationUnit4.saturationTripOut to ActuationUnit2.saturationLogic.channel2;
    // Connect outputs to actuators
    interface SaturationOut : OrGate
      connect ActuationUnit1.saturationLogic.actuate to Actuator2.input;
      connect ActuationUnit2.saturationLogic.actuate to Actuator2.input;
    }
    // TODO : connect the remaining logic
}
