package 'RTS Stakeholders'
{
  // NRC Stakeholders
  part def 'NRC Customer';
  part def 'NRC Assurance SME' :> 'NRC Customer';
  part def 'NRC Certification SME' :> 'NRC Customer';
  
  // Galois Stakeholders
  part def 'Galois Employee' {
    attribute
      name: ScalarValues::String;
      email: ScalarValues::String;
  }
  part def 'Galois PI' :> 'Galois Employee';
  part def 'Galois PL' :> 'Galois Employee';
  part def 'Galois Research Engineer' :> 'Galois Employee'; 
  part def 'Galois Software and Assurance Research Engineer' 
    :> 'Galois Research Engineer';
  part def 'Galois Hardware Research Engineer' :> 'Galois Research Engineer';
  part PI : 'Galois PI' {
    attribute
      redefines name = "Joe Kiniry";
      redefines email = "kiniry@galois.com";
  }
  // @todo kiniry Add details for other performers.
  part PL : 'Galois PL' {
    attribute
      redefines name = "Andrew Bivin";
      redefines email = "abivin@galois.com";    
  } 
  part SARE : 'Galois Software and Assurance Research Engineer' {
    attribute
      redefines name = "Alex Bakst";
      redefines email = "abakst@galois.com";
  }
  part HRE : 'Galois Hardware Research Engineer' {
    attribute
      redefines name = "Michal Podhradsky";
      redefines email = "mpodhradsky@galois.com";
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