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
