package 'RTS Stakeholders'
{
  part def 'NRC Customer';
  part def 'Galois Employee' {
    attribute
      name: ScalarValues::String;
      email: ScalarValues::String;
  }
  part def 'Galois PI' :> 'Galois Employee';
  part def 'Galois PL' :> 'Galois Employee';
  part def 'Galois Research Engineer' :> 'Galois Employee'; 
  part def 'Galois Software Research Engineer' :> 'Galois Research Engineer';
  part def 'Galois Hardware Research Engineer' :> 'Galois Research Engineer';
  part PI : 'Galois PI' {
    attribute
      redefines name = "Joe Kiniry";
      redefines email = "kiniry@galois.com";
  }
  // @todo kiniry Add details for other performers.
  part PL : 'Galois PL' {
    
  } 
  part RSE : 'Galois Software Research Engineer' {
    
  }
  part HSE : 'Galois Hardware Research Engineer' {
    
  }
  
  concern 'requirement traceability' {
    doc /* Will all requirements be traceable from project requirement
         * or NRC characteristic to assurance evidence demonstrated in a
         * report? */
    stakeholder 'Customer';
    stakeholder 'Galois Employee';
  }
  
  // @todo kiniry Express other concerns expressed in the RFP, from the NRC,
  // or from Galois or the Galois HARDENS team.
}