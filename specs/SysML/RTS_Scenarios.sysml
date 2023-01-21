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

/**
 * The set of all scenarios that describe interesting end-to-end executions
 * of the RTS system.  The full set of scenarios must include all normal
 * behavior (online and during self-test) and exceptional behavior.
 */
package <Scenarios> 'RTS Scenarios' {
  package <Normal> 'RTS Normal Behavior Scenarios' {
    import 'RTS Architecture'::'RTS System Architecture'::RTS;

    item def 'RTS User';
    use case def <NB> 'Normal Behavior' {
      subject RTS;
      actor user : 'RTS User';
      objective {
        doc /* @see test_scenarios.lando */
      }
    }
    // @design kiniry Actually, ST should specialize NB.  I don't know how
    // to express that in SysML yet.
    use case def <ST> 'Normal Behavior Under Self-Test' {
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
  package <Exceptional> 'RTS Exceptional Behavior Scenarios' {
    use case def <EB> 'Exceptional Behavior' {
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