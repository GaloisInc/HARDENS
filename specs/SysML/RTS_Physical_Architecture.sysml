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

///** The physical architecture of the HARDENS RTS demonstrator. */
package 'RTS Physical Architecture' {
  import 'Project Glossary'::*;
  import 'RTS Hardware Artifacts'::*;

  /** A PCB developer board used to prototype hardware. */
  part 'HARDENS Demonstrator Board' : DevBoard;
  /** The USB cable used to communicate the ASCII UI to/from the board. */
  part <UI_C> 'USB UI Cable' : 'USB Cable';
  /** The USB cable used to program the board with a bitstream. */
  part <Prog_C> 'USB Programming Cable' : 'USB Cable';
  /** The USB cable used to interact with the board in a debugger. */
  part <Debug_C> 'USB Debugging I/O Cable' : 'USB Cable';
  // @trace #11 https://github.com/GaloisInc/HARDENS/issues/11
  // @todo Add attributes for URL traceability.
  part def <MPL3115A2> 'SparkFun Altitude/Pressure Sensor Breakout' :>
    PCB, 'Pressure Sensor';
  // 4x https://www.sparkfun.com/products/11084
  part def 'SparkFun MOSFET Power Control Kit' :> PCB, Power;
  // 4x https://www.sparkfun.com/products/12959
  part def <TMP102> 'SparkFun Digital Temperature Sensor Breakout' :>
    PCB, 'Temperature Sensor';
  // 4x https://www.sparkfun.com/products/13314
  part def 'Small Push-Pull Solenoid - 12VDC' :> 'Solenoid Actuator';
  // 4x https://www.adafruit.com/product/412
  part def '1N4001 Diode';
  // 1x https://www.adafruit.com/product/755
  /** The first of two redundant temperature sensors. */
  part <TS1> 'Temperature Sensor 1' : TMP102;
  /** The second of two redundant temperature sensors. */
  part <TS2> 'Temperature Sensor 2' : TMP102;
  /** The first of two redundant pressure sensors. */
  part <PS1> 'Pressure Sensor 1' : MPL3115A2;
  /** The second of two redundant pressure sensors. */
  part <PS2> 'Pressure Sensor 2' : MPL3115A2;
  /** The first of two redundant solenoid actuators. */
  part <SA1> 'Solenoid Actuator 1' : 'Small Push-Pull Solenoid - 12VDC';
  /** The second of two redundant solenoid actuators. */
  part <SA2> 'Solenoid Actuator 2' : 'Small Push-Pull Solenoid - 12VDC';
  // @todo kiniry Add ports for external connectors.

  /** The computer used by a developer to interface with the demonstrator,
      typically for driving the demonstrator's UI and programming and
      debugging the board. */
  part 'Developer Machine' : Computer;

  /** The fully assembled HARDENS demonstrator hardware with all component present. */
  part <Demonstrator> 'HARDENS Demonstrator';

  connection def DevMachineToDevBoard {
    end: Computer;
    end: PCB;
  }
  // connection: DevMachineToDevBoard connect 'Developer Machine' to DevBoard;
}
