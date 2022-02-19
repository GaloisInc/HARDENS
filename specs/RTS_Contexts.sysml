package 'RTS System Contexts' {
  import 'RTS Architecture'::*;
  import 'Kiniry RTS System Architecture Draft'::*;
  
  // This specification is meant to frame the RTS in the larger context of
  // deployment into a Nuclear Power Plant.
  
  // Definitions of system contexts.
  
  // Introduce the RTS context.
  part def 'Reactor Trip System Context';
  alias RTSC for 'Reactor Trip System Context';
  
  // Introduce the NPP context.
  part def 'Nuclear Power Plant Context';
  alias NPPC for 'Nuclear Power Plant Context';
  
  part def 'Nuclear Power Plant Operator';
  part def 'Nuclear Power Plant Certifier';
  
  // Definitions of relevant connections
  connection def 'Digital Instrumentation and Control' {
    end: RTSC[1];
    end: NPPC[1];
  }
  alias DIandC for 'Digital Instrumentation and Control';

  connection def 'NPP Operation' {
    end: 'Nuclear Power Plant Operator'[*];
    end: DIandC[1]; 
  }

  connection def 'NPP Certification Authority' {
    end: 'NPPC'[1];
    end: 'Nuclear Power Plant Certifier'[1..*];
  }
}