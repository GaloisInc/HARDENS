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
    part BlueCheck;
    part Coq;
    // etc.
    part id IO 'I/O';
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

%viz RTS

import RTS;
// import Glossary;

package Architecture {
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
            // @bug kiniry Glossary placeholder.
            part CPU;
            part 'RISC-V CPU '[3] :> CPU;
        }
        package Hardware {
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

%viz Architecture

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

// import Glossary;
// import Hardware;

/** The physical hardware components that are a part of the HARDENS RTS
    demonstrator. */
package 'RTS Hardware Artifacts' {
    import ScalarValues::*;

    // @bug kiniry Glossary placeholders.
    part def USB;
    part def Cable;
    part def Connector;
    part def USB_connector :> USB, Connector;
    /** A normal USB cable. */
    part def 'USB Cable' :> USB, Cable {
        /** What kind of USB connector is on the start of the cable? */
        attribute start_connector : USB_connector;
        /** What kind of USB connector is on the end of the cable? */
        attribute end_connector : USB_connector;
    }
    // @bug kiniry Glossary placeholder.
    part PCB;
    part LED;
    part def 'Output_LED' :> LED;
    part def id DevBoard 'FGPA Dev Board' :> PCB {
        // @bug kiniry Glossary placeholder.
        part id J9_J26 'SERDES Test SMA Connector'[16];
        part id J38 'Parallel Config Header';
        part id J39_J40 'Versa Expansion Connector'[2];
        part id U4 'SPI Flag Configuration Memory';
        part id SW1 'CFG Switch';
        part id SW5 'Input Switch';
        part id D5_D12 'Output LED'[8] : 'Output_LED';
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
    
    item def TemperatureValue :> ScalarQuantityValue;
    item def PressureValue :> ScalarQuantityValue;
    port def SensorValuePort {
        out item value: Real;
    }
    part Sensor {
        port value: SensorValuePort;
    }
    /** A sensor that is capable of measuring the temperature of its environment. */
    part 'Temperature Sensor' :> Sensor {
        /** What is your temperature reading in Celcius (C)? */
        port temp: TemperatureValue redefines value;
    }
    /** A sensor that is capable of measuring the air pressure of its environment. */
    part 'Pressure Sensor' :> Sensor {
        /** What is your pressure reading in Pascal (P)? */
        part pressure: PressureValue redefines value;
        
    }
    enum SolenoidState {
        OPEN;
        CLOSED;
    }
    /** A solenoid actuator capable of being in an open or closed state. */
    part 'Solenoid Actuator' :> Actuator {
        item actuator_state: SolenoidState;
        /** Open! */
        port open;
        /** Close! */
        port close;
    }
}

/** The physical architecture of the HARDENS RTS demonstrator. */
package 'Physical Architecture' {
  /** The USB cable used to communicate the ASCII UI to/from the board. */    
  part id UI_C 'USB UI Cable';
}
/*
component USB Programming Cable (Prog-C)
The USB cable used to program the board with a bitstream.

component USB Debugging I/O Cable (Debug-C)
The USB cable used to interact with the board in a debugger.

component Dev Board (Board)
A PCB developer board used to prototype hardware.

// * MOSFET power control kit: https://www.sparkfun.com/products/12959

// * 12 V Latch solenoid: https://www.sparkfun.com/products/15324

// * Pressure sensor: https://www.sparkfun.com/products/11084

component Temperature Sensor 1 (TS1)
The first of two redundant temperature sensors.

component Temperature Sensor 2 (TS2)
The second of two redundant temperature sensors.

component Pressure Sensor 1 (PS1)
The first of two redundatnt pressure sensors.

component Pressure Sensor 2 (PS2)
The second of two redundant pressure sensors.

component Solenoid Actuator 1 (SA1)
The first of two redundant solenoid actuators.

component Solenoid Actuator 2 (SA2)
The second of two redundant solenoid actuators.

component HARDENS Demonstrator (Demonstrator)
The fully assembled HARDENS demonstrator hardware with all component
present.

relation Demonstrator client Board
relation Board client UI
relation Board client UI-C
relation Board client Prog-C
relation Board client Debug-C
relation Board client TS1
relation Board client TS2
relation Board client PS1
relation Board client PS2
relation Board client SA1
relation Board client SA2

component Developer Machine
The computer used by a developer to interface with the demonstrator,
typically for driving the demonstrator's UI and programming and
debugging the board.

relation UI-C client Developer Machine
relation Prog-C client Developer Machine
relation Debug-C client Developer Machine
*/


