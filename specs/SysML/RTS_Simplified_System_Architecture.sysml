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

package 'RTS Simplified System Architecture' {
  private import 'Project Glossary'::*;

  // doc id sys_arch_doc
  package Root {
    part def <CFSM> 'Core Finite State Machine' :> FSM;
    part def <Programming_IO> 'Programming I/O' :> IO;
    part def <UI_IO> 'UI I/O' :> IO;
    part def <Debugging_IO> 'Debugging I/O' :> IO;
  }
  package 'Actuation_Logic' {
    part 'Voting Logic': 'Voting'[2];
    part 'Actuator Logic': 'Actuator'[2];
  }
  /** Documentation about computation goes here. */
  package Computation {
    part def 'RISC-V CPU':> CPU, RISC_V_ISA;
    part <CPUs> 'RISC-V CPUs': 'RISC-V CPU'[3];
  }
  package Hardware {
    package FPGA {
      part <DevBoard> 'Lattic ECP-5 FPGA Development Board': PCB;
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
    part def Instrumentation;
    part I: 'Instrumentation'[4];
  }

  package RTS {
    part def Base_RTS_Architecture_Context {
      // part ref
    }
  }
}
