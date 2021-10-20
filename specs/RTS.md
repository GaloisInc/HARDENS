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

```
package 'Semantic Properties' {
    doc /* Semantic Properties are used to document arbitrary constructs
           in our specifications.
           @see https://www.kindsoftware.com/documents/whitepapers/code_standards/properties.html
         */
    import ScalarValues::*;

    /* @todo kiniry The scope of every attribute needs to be tightened. */
    /* @todo kiniry Many properties' types must be refined. */

    attribute def AuthorDescription {
        attribute author: String;
        attribute description: String;
    }

    package 'Meta-Information' {
        attribute author: String;
        attribute lando: String;
        attribute bug: String;
        attribute copyright: String;
        attribute description: String;
        attribute history: String;
        attribute license: String;
        attribute title: String;
    }

    package 'Pending Work' {
        /** @todo to be refined according to definition */
        attribute idea: String;
        attribute review: String;
        attribute todo: String;
    }

    private part def RichAssertion {
        attribute label: String;
        attribute expression: Boolean;
        // attribute exception: Exception/Signal;
        attribute description: String;
    }

    private part def ExpressionDescriptionPair {
        attribute expression: Boolean;
        attribute definition: String;
    }
    
    enum def ModifiesFrame {
        SINGLE_ASSIGNMENT;
        QUERY;
        EXPRESSION;
    }
    package 'Formal Specifications' {
        attribute ensures: Boolean;
        attribute generate: Boolean;
        attribute invariant: Boolean;
        attribute modify: Boolean;
        attribute requires: Boolean;
    }
    
    package 'Concurrency Control' {
        attribute concurrency: Boolean;
    }
    
    package 'Usage Information' {
        attribute param: Boolean;
         // Note that we rename 'return' to 'result' to avoid SysML keyword conflict.
        attribute result: Boolean;
        attribute exception: Boolean;        
    }
    
    package Versioning {
        attribute version: String;
        attribute deprecated: String;
        attribute since: String;
    }
    
    package Inheritance {
        attribute hides: String;
        attribute overrides: String;
    }
    
    package Documentation {
        attribute design: String;
        attribute equivalent: Boolean;
        attribute example: String;
        attribute see: String;
    }
    
    package Dependencies {
        attribute references: Boolean;
        // Note that we rename 'use' to 'uses' to avoid SysML keyword conflict.
        attribute uses: Boolean;
    }
    
    package Miscellaneous {
        attribute guard: Boolean;
        attribute vales: Boolean;
        attribute time_complexity: Boolean;
        attribute space_complexity: Boolean;
    }
}

package id Glossary 'Proposal Glossary' {
    /** A formal, state-based specification language that focuses on the
        specification of the interfaces of discrete modules in a system, and
        often times includes model-based specification constructs to improve
        usability and expressivity. */
    part id BISL 'Behavioral Interface Specification Language';
    part def BlueCheck;
    part def Computer;
    part def Coq;
    part def Cryptol;
    part def DevSecOps;
    part def id DIANC 'Digital Instrumentation and Control Systems';
    /** The NASA Formal Requirements Elicitation Tool is used to make writing,
        understanding, and debugging formal requirements natural and
        intuitive. */
    part def id FRET 'Formal Requirements Elicitation Tool';
/** A specification language integrated with support tools and an
automated theorem prover, developed at the Computer Science Laboratory
of SRI International.  PVS is based on a kernel consisting of an
extension of Church's theory of types with dependent types, and is
fundamentally a classical typed higher-order logic. */
    part def PVS;
/** RISC-V (pronounced ``risk-five'') is an open standard instruction set
architecture (ISA) based on established reduced instruction set
computer (RISC) principles. Unlike most other ISA designs, the RISC-V
ISA is provided under open source licenses that do not require fees to
use. A number of companies are offering or have announced RISC-V
hardware, open source operating systems with RISC-V support are
available and the instruction set is supported in several popular
software toolchains. */
    part def RISC_V;
/** A formal specification language that uses hierarchical finite state
machines to specify system requirements. */
part def id RSML 'Requirements State Modeling Language';
/** The Boolean satisfiability problem (sometimes called propositional
satisfiability problem and abbreviated SAT) is the problem of
determining if there exists an interpretation that satisfies a given
Boolean formula. */
    part def SAT;
/** The proof script language is used to specify the assumptions and proof
goals of formal verifications to the SAW tool. */
    part def SAWscript;
/** A CPU or SoC that is implemented in an HDL and synthesized to a
bitstream and loaded onto an FPGA. */
    part def soft_core;
/** A formally defined computer programming language based on the Ada
programming language, intended for the development of high integrity
software used in systems where predictable and highly reliable
operation is essential. It facilitates the development of applications
that demand safety, security, or business integrity. */
    part def SPARK;
/* An integrated development environment for formally specifying and
rigorously analyzing requirements. */
    part def SpeAR;
/** VCC is a program verification tool that proves correctness of
annotated concurrent C programs or finds problems in them. VCC extends
C with design by contract features, like pre- and postcondition as
well as type invariants. Annotated programs are translated to logical
formulas using the Boogie tool, which passes them to an automated SMT
solver Z3 to check their validity. */
    part def id VCC 'Verifier for Concurrent C';
/** A software toolchain that includes static analyzers to check
assertions about a C program; optimizing compilers to translate a C
program to machine language; and operating systems and libraries to
supply context for the C program. The Verified Software Toolchain
project assures with machine-checked proofs that the assertions
claimed at the top of the toolchain really hold in the
machine-language program, running in the operating-system context. */
    part def id VST 'Verified Software Toolchain';

    part def Refinement;
    part def Property;
    part def 'Safety Property' :> Property;
    part def 'Correctness Property' :> Property;
    part def 'Security Property' :> Property;
    part def Model;
    part def 'Semi-Formal Model' :> Model;
    part def 'Formal Model' :> Model;
    part def Consistent :> Property;
    part def Complete :> Property;
    part def 'Consistent Model' :> Consistent, Model;
    part def 'Complete Model' :> Complete, Model;
    part def 'Consistent and Complete Model' :> 'Consistent Model', 'Complete Model';
    part def Requirement;
    part def Scenario;
    part def Product;
    part def 'Product Line';
    part def Configure;
    part def DOORS;
    part def Clafer;
    part def Lobot;
    part def Denotational;
    part def Operational;
    part def Semantics;
    part def Risk;
    part def Power;
    part def Resource;
    part def Reliability;
    /** A specification that has a precise, unambiguous, formal semantics
        grounded in real world formal foundations and systems engineering
        artifacts, such as source code and hardware designs. */
    part def Rigorous;
    part def id CDE 'Collaborative Development Environment';
    part def id CI 'Continuous Integration';
    part def id CV 'Continuous Verification';
    part def Analyzer;
    part def 'Static Analyzer' :> Analyzer;
    part def 'Dynamic Analyzer' :> Analyzer;
    part def id FSM 'Finite State Machine';
    part def Deterministic;
    part def 'Non-deterministic';
    part def id DFSM 'Deterministic Finite State Machine' :> FSM, Deterministic;
    part def id NFSM 'Non-deterministic Finite State Machine' :> FSM, 'Non-deterministic';
    part def id ASM 'Abstract State Machine';
    part def Design;
    part def Architecture;
    part def Specification;
    part def 'Architecture Specification' :> Specification;
    part def Solver;
    part def id FM 'Formal Method';
    part def id LF 'Logical Framework';
    part def id PL 'Programming Language';
    part def 'Specification Language';
    part def Protocol;
    part def 'System Specification' :> Specification;
    part def 'Hand-written';
    part def 'Machine-generated';
    part def 'Source-level Specification Language' :> 'Specification Language';
    part def 'Model-based Specification Language' :> 'Specification Language';
    part def System;
    part def 'Distributed System' :> System;
    part def 'Concurrent System' :> System;
    part def 'Cryptographic Protocol' :> Protocol;
    part def 'Cryptographic Algorithm';
    part id IO 'I/O';
    part id GPIO 'General Purpose I/O';
    part def Sensor;
    part def Actuator;
    part def Solenoid :> Actuator;
    part def Compiler;
    part def Synthesizer;
    part def id USB 'Universal Serial Bus';
    part def LED;
    part def Cable;
    part def Program;
    part def Bitstream;
    part def id FPGA 'Field-Programmable Gate Array';
    part def 'ECP-5' :> FPGA;
    part def id PCB 'Printed Circuit Board';
    part def Connector;
    part def 'USB Connector' :> USB, Connector;
    part def id USB_Mini 'USB Mini Connector' :> 'USB Connector';
    part def 'High-Assurance';
    part def C :> 'Programming Language';
    part def PMOD;
    part def JTAG;
    part def Driver;
    part def Voting;
    /** A normal USB cable. */
    part def 'USB Cable' :> USB, Cable {
        /** What kind of USB connector is on the start of the cable? */
        part def start_connector :> 'USB Connector';
        /** What kind of USB connector is on the end of the cable? */
        part def end_connector :> 'USB Connector';
    }
    part def 'Output LED' :> LED;
}

package id RTS 'Reactor Trip System' {
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

package Architecture {
    import RTS;
    /** Note that this is the *systems* architecture, 
        which is different than our software, harddware, 
        or data architectures. */
    package id RTS_System_Arch 'RTS System Architecture' { 
        // doc id sys_arch_doc
        // @bug kiniry Placeholders until we figure out how to import Glossary.
        part FSM;
        part IO;
        package Root {
            part id CFSM 'Core Finite State Machine' :> FSM;
            part id Programming_IO 'Programming I/O' :> IO;
            part id UI_IO 'UI I/O' :> IO;
            part id Debugging_IO 'Debugging I/O' :> IO;
        }
        package 'Actuation_Logic' {
            part 'Voting'[2];
            part 'Actuator'[2];
        }
        /** Documentation about computation goes here. */
        package Computation {
            // @bug kiniry Placeholders until we figure out how to import Glossary.
            part CPU;
            part 'RISC-V CPU '[3] :> CPU;
        }
        package Hardware {
            // @bug kiniry Placeholders until we figure out how to import Glossary.
            part PCB;
            package FPGA {
                part 'Lattic ECP-5 FPGA Development Board' :> PCB;
            }
            package Actuators {
                part 'Actuator'[2];
            }
            package Sensors {
                // @bug kiniry Glossary placeholder.
                part Sensor;
                part 'Temperature Sensor'[2] :> Sensor;
                part 'Pressure Sensor'[2] :> Sensor;
            }
        }
        package Instrumentation {
            part 'Instrumentation'[4];

        }
    }
}

package Artifacts {
    part CryptolSpec;
    part CryptolToC;
    part CryptolToSystemVerilog;
    part Software;
    part SWImpl;
    part SynthSW;
    part Hardware;
    part HWImpl;
    part SynthHW;
    part CPU;
    part CompCert;
    part BSC;
    part SymbiFlow;
    part Binaries;
    part RTL;
    part Bitstream;
    package Dataflow;
}

/** The physical hardware components that are a part of the HARDENS RTS
    demonstrator. */
package 'RTS Hardware Artifacts' {
    import Glossary::*;
    import Architecture::RTS_System_Arch::Hardware::*;
    import ScalarValues::*;

    part def id DevBoard 'FGPA Dev Board' :> PCB {
        part id J9_J26 'SERDES Test SMA Connector'[16];
        part id J38 'Parallel Config Header';
        part id J39_J40 'Versa Expansion Connector'[2];
        part id U4 'SPI Flag Configuration Memory';
        part id SW1 'CFG Switch';
        part id SW5 'Input Switch';
        part id D5_D12 'Output LED'[8];
        part id SW2_SW4 'Input Push Button'[3];
        part id J37 '12 V DC Power Input';
        part id J5_J8_J32_J33 'GPIO Headers'[4];
        part id J31 'PMOD/GPIO Header';
        part id J30 'Microphone Board/GPIO Header';
        part 'Prototype Area';
        part FPGA;
        part id U3 'ECP5-5G Device' :> FPGA;
        part id J1 'JTAG Interface';
        part id J2 'Mini USB Programming';
        part id Board 'Lattice ECP-5 FPGA Development Board';
    }
    
    item def TemperatureValue :> Real;
    item def PressureValue :> Real;
    port def SensorValuePort {
        out item value;
    }
    part Sensor {
        port value: SensorValuePort;
    }
    /** A sensor that is capable of measuring the temperature of its environment. */
    part 'Temperature Sensor' :> Sensor {
        /** What is your temperature reading in Celcius (C)? */
        port temp redefines value;
    }
    /** A sensor that is capable of measuring the air pressure of its environment. */
    part 'Pressure Sensor' :> Sensor {
        /** What is your pressure reading in Pascal (P)? */
        part pressure: PressureValue redefines value;
        
    }
    enum def SolenoidState {
        OPEN;
        CLOSED;
    }
    /** A solenoid actuator capable of being in an open or closed state. */
    part def 'Solenoid Actuator' :> Actuator {
        item actuator_state;
        /** Open! */
        port open;
        /** Close! */
        port close;
    }
}

/** The physical architecture of the HARDENS RTS demonstrator. */
package 'Physical Architecture' {
    import Glossary::*;
    /** A PCB developer board used to prototype hardware. */
    part def id Board 'Dev Board' :> PCB {
        /** The USB cable used to communicate the ASCII UI to/from the board. */    
        part def id UI_C 'USB UI Cable';
        /** The USB cable used to program the board with a bitstream. */
        part def id Prog_C 'USB Programming Cable';
        /** The USB cable used to interact with the board in a debugger. */
        part def id Debug_C 'USB Debugging I/O Cable';
        // * MOSFET power control kit: https://www.sparkfun.com/products/12959
        // * 12 V Latch solenoid: https://www.sparkfun.com/products/15324
        // * Pressure sensor: https://www.sparkfun.com/products/11084
        /** The first of two redundant temperature sensors. */
        part def id TS1 'Temperature Sensor 1';
        /** The second of two redundant temperature sensors. */
        part def id TS2 'Temperature Sensor 2';
        /** The first of two redundatnt pressure sensors. */
        part def id PS1 'Pressure Sensor 1';
        /** The second of two redundant pressure sensors. */
        part def id PS2 'Pressure Sensor 2';
        /** The first of two redundant solenoid actuators. */
        part def id SA1 'Solenoid Actuator 1';
        /** The second of two redundant solenoid actuators. */
        part def id SA2 'Solenoid Actuator 2';
        // @todo kiniry Add ports for external connectors.
    }
    /** The fully assembled HARDENS demonstrator hardware with all component present. */
    part def id Demonstrator 'HARDENS Demonstrator';

    /** The computer used by a developer to interface with the demonstrator,
        typically for driving the demonstrator's UI and programming and
        debugging the board. */
    part def 'Developer Machine' :> Computer;

    connection def DevMachineToDevBoard {
        end: Computer;
        end: PCB;
    } 
//    connection: DevMachineToDevBoard connect 'Developer Machine' to Board;
}
```

%viz "Architecture"

%viz --view=tree "Reactor Trip System"

%viz "RTS Hardware Artifacts"

