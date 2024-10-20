// Copyright 2021, 2022, 2023 Galois, Inc.
// Copyright 2022 Rishiyur Nikhil
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package Actuation_Generated_BVI;

import Clocks :: *;
import Actuation::*;

(* synthesize *)
module mkActuationGenerated(Actuation_IFC);
    ActuationD0_IFC a0 <- mkActuationGeneratedD0();
    ActuationD1_IFC a1 <- mkActuationGeneratedD1();

    interface ActuationD0_IFC d0;
        method actuate_d0 = a0.actuate_d0();
    endinterface
    interface ActuationD1_IFC d1;
        method actuate_d1 = a1.actuate_d1();
    endinterface
endmodule

import "BVI" Actuate_D0 =
module mkActuationGeneratedD0 (ActuationD0_IFC);
    default_clock ();
    default_reset ();

    method out actuate_d0 (trips, old);
    schedule (actuate_d0) CF (actuate_d0);
endmodule

import "BVI" Actuate_D1 =
module mkActuationGeneratedD1 (ActuationD1_IFC);
    default_clock ();
    default_reset ();

    method out actuate_d1 (trips, old);
    schedule (actuate_d1) CF (actuate_d1);
endmodule

endpackage
