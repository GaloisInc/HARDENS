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

package 'RTS System Contexts' {
  import 'RTS Architecture'::*;

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