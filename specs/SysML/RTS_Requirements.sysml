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
 * All requirements that the RTS system must fulfill, as driven by the
 * IEEE 603-2018 standards and the NRC RFP.
 */
package <Requirements> 'RTS Requirements' {
  // Note that we do not specify documentation comments here as they
  // are specified in the Lando specification.  If we do not include
  // additional specifications here on the refinement from the higher-level
  // specification (in this case, SysML refines Lando), then the higher-level
  // specification's comments/specifications refine too (an hence are
  // just copied verbatim).
  package <Requirements> 'HARDENS Project High-level Requirements' {
    import 'Project Glossary'::*;
    import 'RTS Stakeholders'::*;

    requirement def 'Project Requirements' {
      subject 'NRC staff' : 'NRC Customer';
    }
    requirement 'NRC Understanding' : 'Project Requirements';
    requirement 'Identify Regulatory Gaps' : 'Project Requirements';
    requirement Demonstrate : 'Project Requirements';
    requirement 'Demonstrator Parts' : 'Project Requirements';
    requirement 'Demonstrator Groundwork' : 'Project Requirements';
 }
 // @todo kiniry These requirements must be made consistent, or merged with
 // those found in the Characteristics specification.
 package <Characteristics> 'NRC Characteristics' {
   import 'Project Glossary'::*;
   import 'RTS Stakeholders'::*;

   requirement def 'NRC Characteristic' {
     //subject expert: 'NRC Certification SME';
     //subject regulation: 'NRC Certification Regulations';
   }
   requirement 'Requirements Consistency' : 'NRC Characteristic';
   requirement 'Requirements Colloquial Completeness' : 'NRC Characteristic';
   requirement 'Requirements Formal Completeness' : 'NRC Characteristic';
   requirement 'Instrumentation Independence' : 'NRC Characteristic';
   requirement 'Channel Independence' : 'NRC Characteristic';
   requirement 'Actuation Independence' : 'NRC Characteristic';
   requirement 'Actuation Correctness' : 'NRC Characteristic';
   requirement 'Self-Test/Trip Independence' : 'NRC Characteristic';
 }
 // Note that formal requirements expressed externally must be traceable
 // to this system model, but need not be repeated in whole here.  Model
 // elements that are expressed in both the SysML and FRET models must
 // be in a refinement relationship with each other (e.g,, in this case study,
 // SysML ⊑ FRET.
 package 'Formal Requirements' {
   import 'Project Glossary'::*;
   requirement def <FRET> 'FRET Requirements' {
     doc /* RTS requirements formalized in the FRET tool. */
   }
   // @todo kiniry Complete remaining FRET requirements.
   requirement ACTUATION_ACTUATOR_0 : FRET;
 }
}