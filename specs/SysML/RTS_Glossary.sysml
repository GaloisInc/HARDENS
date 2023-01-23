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

/*
 # Reactor Trip System (RTS) High-assurance Demonstrator
 ## project: High Assurance Rigorous Digital Engineering for Nuclear Safety (HARDENS)
 ### copyright (C) 2021-2022 Galois
 ### author: Joe Kiniry <kiniry@galois.com>
*/

// @see https://github.com/GaloisInc/HARDENS/issues/30

package <Glossary> 'Project Glossary' {
  // @design Eliminate all redundancy with concepts in KerML or SysML domain
  // libraries.
  private import ScalarValues::*;
  private import KerML::*;

  // Original proposal glossary.
  part def BlueCheck;
  /** A formal, state-based specification language that focuses on the
      specification of the interfaces of discrete modules in a system, and
      often times includes model-based specification constructs to improve
      usability and expressivity. */
  abstract item <BISL> 'Behavioral Interface Specification Language';
  abstract part def Computer;
  abstract part def Coq;
  abstract part def Cryptol;
  abstract item def DevSecOps;
  abstract item def <DIANC> 'Digital Instrumentation and Control Systems';
  /** The NASA Formal Requirements Elicitation Tool is used to make writing,
      understanding, and debugging formal requirements natural and
      intuitive. */
  part def <FRET> 'Formal Requirements Elicitation Tool';
  /** An Instruction Set Architecture, or ISA for short, is the set of
      instructions that a given kind of CPU can understand. Example ISAs
      include x86, x64, MIPS, RISC, RISC-V, AVR, etc. */
  attribute def <ISA> 'Instruction Set Architecture';
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
  part def RISC_V_ISA :> ISA;
  /** A formal specification language that uses hierarchical finite state
      machines to specify system requirements. */
  part def <RSML> 'Requirements State Modeling Language';
  /** The Boolean satisfiability problem (sometimes called propositional
      satisfiability problem and abbreviated SAT) is the problem of
      determining if there exists an interpretation that satisfies a given
      Boolean formula. */
  abstract item def SAT;
  /** The proof script language is used to specify the assumptions and proof
      goals of formal verifications to the SAW tool. */
  part def SAWscript;
  /** A CPU or SoC that is implemented in an HDL and synthesized to a
      bitstream and loaded onto an FPGA. */
  abstract item def 'Soft Core' {
    // size: estimated number of gates
    // complexity: measured complexity metric
    // hdls: which HDLs are used in the design
  }
  /** A formally defined computer programming language based on the Ada
      programming language, intended for the development of high integrity
      software used in systems where predictable and highly reliable
      operation is essential. It facilitates the development of applications
      that demand safety, security, or business integrity. */
  part def SPARK;
  /** An integrated development environment for formally specifying and
      rigorously analyzing requirements. */
  part def SpeAR;
  /** VCC is a program verification tool that proves correctness of
      annotated concurrent C programs or finds problems in them. VCC extends
      C with design by contract features, like pre- and postcondition as
      well as type invariants. Annotated programs are translated to logical
      formulas using the Boogie tool, which passes them to an automated SMT
      solver Z3 to check their validity. */
  part def <VCC> 'Verifier for Concurrent C';
  /** A software toolchain that includes static analyzers to check
      assertions about a C program; optimizing compilers to translate a C
      program to machine language; and operating systems and libraries to
      supply context for the C program. The Verified Software Toolchain
      project assures with machine-checked proofs that the assertions
      claimed at the top of the toolchain really hold in the
      machine-language program, running in the operating-system context. */
  part def <VST> 'Verified Software Toolchain';

  // Mathematical modeling concepts in RDE.
  abstract item def Refinement:> Relationship;
  abstract item def Property:> BooleanExpression;
  abstract item def 'Safety Property' :> Property;
  abstract item def 'Correctness Property' :> Property;
  abstract item def 'Security Property' :> Property;
  abstract item def Model;
  abstract item def 'Semi-Formal Model' :> Model;
  abstract item def 'Formal Model' :> Model;
  abstract item def Consistent:> Property;
  abstract item def Complete:> Property;
  abstract item def 'Consistent Model' :> Consistent, Model;
  abstract item def 'Complete Model' :> Complete, Model;
  abstract item def 'Consistent and Complete Model' :> 'Consistent Model', 'Complete Model';
  abstract item def Denotational;
  abstract item def Operational;
  abstract item def Semantics;
  /** A specification that has a precise, unambiguous, formal semantics
      grounded in real world formal foundations and systems engineering
      artifacts, such as source code and hardware designs. */
  abstract item def Rigorous;
  abstract item def Deterministic;
  abstract item def 'Non-deterministic';
  abstract part def <FM> 'Formal Method';

  // Systems modeling concepts in RDE.
  // @design Probably in KerML or SysML domain libraries.
  abstract item def Requirement;
  abstract item def Scenario;
  abstract item def Product;
  abstract item def 'Product Line';
  abstract item def Configure;
  part def DOORS;
  part def Clafer;
  part def Lobot;
  abstract item def <FSM> 'Finite State Machine';
  abstract item def <DFSM> 'Deterministic Finite State Machine'
    :> FSM, Deterministic;
  abstract item def <NFSM> 'Non-deterministic Finite State Machine'
    :> FSM, 'Non-deterministic';
  abstract item def <ASM> 'Abstract State Machine';
  abstract part def Design;
  abstract part def Architecture;
  abstract part def Specification;
  abstract part def 'Architecture Specification' :> Specification;
  abstract part def System;
  abstract part def 'Distributed System' :> System;
  abstract part def 'Concurrent System' :> System;
  abstract part def Algorithm;
  abstract part def Program;

  // Concepts related to measurable abstractions of systems.
  abstract item def Risk;
  abstract item def Power;
  abstract item def Resource;
  abstract item def Reliability;

  // Assurance concepts and techonlogies.
  abstract item def <CDE> 'Collaborative Development Environment';
  abstract item def <CI> 'Continuous Integration';
  abstract item def <CV> 'Continuous Verification';
  abstract item def Analyzer;
  abstract item def 'Static Analyzer' :> Analyzer;
  abstract item def 'Dynamic Analyzer' :> Analyzer;
  abstract part def Solver;
  abstract part def <LF> 'Logical Framework';
  abstract item def 'High-Assurance';

  // Concepts relevant to languages and protocols.
  abstract part def Language;
  abstract part def 'Specification Language' :> Language;
  abstract part def Protocol;
  abstract part def 'System Specification' :> Specification;
  abstract item def 'Hand-written';
  abstract item def 'Machine-generated';
  abstract part def 'Source-level Specification Language'
    :> 'Specification Language';
  abstract part def 'Model-based Specification Language'
    :> 'Specification Language';
  abstract item def Cryptological;
  abstract item def 'Cryptographic Protocol' :> Protocol, Cryptological;
  abstract item def 'Cryptographic Algorithm' :> Algorithm, Cryptological;

  // Software engineering.
  abstract item def <PL> 'Programming Language' :> Language;
  abstract item def 'Source Code';
  abstract part def C :> 'Programming Language';
  abstract part def C_Source :> C, 'Source Code';
  abstract item def 'Object Code';
  abstract item def <IR> 'Intermediate Representation';
  abstract item def <LLVM> 'Low-Level Virtual Machine' :> IR;
  abstract item def Compiler {
    item input: Language[1..*];
    item output: Language[1..*];
  }

  // Hardware design.
  abstract item def Hardware;
  abstract item def SWaP {
    // attribute size:
    // attribute weight:
    // attribute power:
  }
  abstract item def Hard :> SWaP;
  abstract item def 'Soft Core Hardware' :> Hardware, 'Soft Core';
  abstract item def 'Physical Hardware' :> Hardware, Hard;
  abstract part def Synthesizer :> Compiler;
  abstract item def <HDL> 'Hardware Design Language';
  abstract part def BluespecSystemVerilog :> HDL;
  abstract part def SystemVerilog :> HDL;
  abstract part def Verilog :> SystemVerilog;
  abstract part def Chisel :> HDL;
  abstract part def <CPU> 'Central Processing Unit';

  // Hardware engineering concepts.
  abstract part def Component;
  abstract part def Switch :> Component;
  abstract part def Button :> Component;
  abstract part def Header :> Component;
  abstract part def Interface :> Component;
  abstract part def Connector :> Component;
  abstract part def Memory :> Component;
  abstract part def ASIC :> Component;
  abstract item def <IO> 'I/O';
  abstract part def <GPIO> 'General Purpose I/O';
  abstract part def Sensor;
  abstract part def 'Temperature Sensor';
  abstract part def 'Pressure Sensor';
  abstract part def Actuator;
  abstract part def Solenoid :> Actuator;
  abstract item def Bus;
  abstract part def <USB> 'Universal Serial Bus' :> Bus;
  abstract part def LED;
  abstract part def Cable;
  abstract part def <FPGA> 'Field-Programmable Gate Array' :> ASIC;
  abstract part def 'ECP-5' :> FPGA;
  abstract part def <PCB> 'Printed Circuit Board' {
    part components: Component[*];
  }
  abstract part def 'USB Connector' :> USB, Connector;
  abstract part def <USB_Mini> 'USB Mini Connector' :> 'USB Connector';
  abstract part def PMOD;
  abstract part def JTAG:> Protocol;
  abstract part def Driver;
  port def USB_In {
    in item 'USB Connector';
  }
  port def USB_Out {
    out item 'USB Connector';
  }
  /** A normal USB cable. */
  abstract part def 'USB Cable' :> USB, Cable {
    /** What kind of USB connector is on the start of the cable? */
    port start_connector: USB_In;
    /** What kind of USB connector is on the end of the cable? */
    port end_connector: USB_Out;
  }
  port def 'Output LED' :> LED;

  // Safety-critical concepts.
  abstract item def Voting;

  // Artifacts specific to RDE.
  abstract part def <CryptolSpec> 'Cryptol System Specification'
   :> Cryptol, 'System Specification' {
     attribute literate: Boolean;
   }
  attribute def Languages {
    attribute languages: String[*];
  }
  abstract part def <Impl> 'Implementation' {
    attribute languages: Languages[*];
  }
  abstract part def <Software> 'Software Implementation'
    :> Implementation;
  abstract part def <SWImpl> 'Hand-written Software Implementation'
    :> Software, 'Hand-written';
  abstract part def <SynthSW> 'Synthesized Software Implementation'
    :> Software, 'Machine-generated';
  abstract part def 'Hardware Implementation';
  abstract part def <HWImpl> 'Hand-written Hardware Implementation';
  abstract part def <SynthHW> 'Synthesized Hardware Implementation';
  abstract part def <Binary> 'Software Binaries' {
    attribute verified_compilation: Boolean;
    attribute secure_compilation: Boolean;
    attribute isa: ISA;
  }
  part def RISCV_Binary :> Binary {
    // :>> isa = RISC_V_ISA;
  }
  abstract part def <Bitstream> 'FPGA Bitstream' {
    attribute proprietary_flow: Boolean;
  }

  // NRC concepts.
  abstract part def 'NRC Certifcation Regulations';
}
