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

/* RTS_Hardware_Artifacts.sysml*/
/**
 * The physical hardware components that are a part of the HARDENS RTS
 * demonstrator.
 */
package 'RTS Hardware Artifacts' {
  private import 'Project Glossary'::*;
  import 'RTS Instrumentation Physical Architecture'::*;
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
  part def <DevBoard> 'Lattice ECP-5 FPGA Development Board' :> PCB {
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