/**
 * All requirements that the RTS system must fulfill, as driven by the
 * IEEE 603-2018 standards and the NRC RFP.
 */
package id Requirements 'RTS Requirements' {
  // Note that we do not specify documentation comments here as they
  // are specified in the Lando specification.  If we do not include
  // additional specifications here on the refinement from the higher-level
  // specification (in this case, SysML refines Lando), then the higher-level
  // specification's comments/specifications refine too (an hence are 
  // just copied verbatim).
  package id Requirements 'HARDENS Project High-level Requirements' {
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
 package id Characteristics 'NRC Characteristics' {
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
   requirement def id FRET 'FRET Requirements' {
     doc /* RTS requirements formalized in the FRET tool. */     
   }
   // @todo kiniry Complete remaining FRET requirements.
   requirement ACTUATION_ACTUATOR_0 : FRET;
 }
}