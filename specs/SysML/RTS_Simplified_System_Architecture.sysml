package 'RTS Simplified System Architecture' {
  private import 'Project Glossary'::*;

  // doc id sys_arch_doc
  package Root {
    part def id CFSM 'Core Finite State Machine' :> FSM;
    part def id Programming_IO 'Programming I/O' :> IO;
    part def id UI_IO 'UI I/O' :> IO;
    part def id Debugging_IO 'Debugging I/O' :> IO;
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
    part def Instrumentation;
    part I: 'Instrumentation'[4];
  }
  
  package RTS {
    part def Base_RTS_Architecture_Context {
      // part ref 
    }
  }
}
