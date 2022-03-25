/*
 # Reactor Trip System (RTS) High-assurance Demonstrator
 ## project: High Assurance Rigorous Digital Engineering for Nuclear Safety (HARDENS)
 ### copyright (C) 2021 Galois
 ### author: Joe Kiniry <kiniry@galois.com>
*/

/**
 * The overall shape of the Reactor Trip System (RTS) is an archetypal
 * *sense-compute-actuate* architecture. Sensors are in the `Sensors`
 * subsystem. They are read by the `Instrumentation` subsystem, which
 * contains four separate and independent `Instrumentation`
 * components. The "Compute" part of the architecture is spread across
 * the `Actuation Logic` subsystem—which contains the two `Voting`
 * components which perform the actuation logic itself—and the `Root`
 * subsystem which contains the core computation and I/O components, and
 * the two separate and independent devices that drive actuators.
 */
package id RTS 'Reactor Trip System' {
  private import 'Semantic Properties'::*;
  import 'Project Glossary'::*;
  import 'RTS Viewpoints and Views'::*;
  import 'RTS Architecture'::*;
  
  
  package id Architecture 'RTS Architecture';
  alias Arch for Architecture;
  package id Hardware 'RTS Hardware Artifacts';
  alias HW for Hardware;
  package id Artifacts 'RTS Implementation Artifacts';
  package id Requirements 'RTS Requirements';
  package id Properties 'RTS Properties';
  alias Props for Properties;
  package id Characteristics 'IEEE Std 603-2018 Characteristics';
  comment TopLevelPackages about Architecture, Hardware, Properties, Characteristics
  /* These are the core top-level subsystems characterizing HARDEN work. */
}
