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

package Actuation;

import Vector :: *;

// Actuation interface
interface Actuation_IFC;
    interface ActuationD0_IFC d0;
    interface ActuationD1_IFC d1;
endinterface

interface ActuationD0_IFC;
    (* always_ready *)
    method Bool actuate_d0 (Vector#(3, Bit#(32)) trips,
                            Bool old);
endinterface

interface ActuationD1_IFC;
    (* always_ready *)
    method Bool actuate_d1 (Vector#(3, Bit#(32)) trips,
                            Bool old);
endinterface

endpackage
