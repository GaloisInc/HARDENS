// Copyright 2021, 2022, 2023 Galois, Inc.
// Copyright 2022 Bluespec, Inc.
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

// Copyright (c) 2022 Rishiyur S. Nikhil

package Nerv;

// ================================================================
// Module mkNerv is a thin wrapper around mkNerv_BVI to make DMem
// outputs (strobe and data) into a struct

// ================================================================
// Import from BSV library

// None

// ================================================================
// Local imports

import Nerv_BVI :: *;

// ================================================================
// Interface for nerv as we might like to see it in BSV

typedef struct {
   Bit #(4)  wstrb;
   Bit #(32) wdata;
   }
DmemWrite
deriving (Bits, Eq, FShow);

interface Nerv_IFC;
   (* always_ready, always_enabled *)
   method Action m_stall (Bool b);
   (* always_ready *)
   method Bool m_trap;

   (* always_ready *)
   method Bit #(32) m_imem_addr;
   (* always_ready, always_enabled *)
   method Action m_imem_data (Bit #(32) xi);

   method Bit #(32) m_dmem_addr;
   method DmemWrite m_get_dmem;
   
   (* always_ready, always_enabled *)
   method Action m_dmem_rdata (Bit #(32) xd);

   method Bool m_dmem_valid;
endinterface

// ================================================================

(* synthesize *)
module mkNerv (Nerv_IFC);

   Nerv_BVI_IFC nerv_BVI <- mkNerv_BVI;

   method Action m_stall (Bool b) = nerv_BVI.m_stall (b);

   method Bool m_trap = nerv_BVI.m_trap;
   method Bool m_dmem_valid = nerv_BVI.m_dmem_valid;

   method Bit #(32) m_imem_addr = nerv_BVI.m_imem_addr;
   method Action m_imem_data (Bit #(32) xi) = nerv_BVI.m_imem_data (xi);

   method Bit #(32) m_dmem_addr () if (nerv_BVI.m_dmem_valid);
      return nerv_BVI.m_dmem_addr;
   endmethod

   method DmemWrite m_get_dmem () if (nerv_BVI.m_dmem_valid);
      return DmemWrite {wstrb: nerv_BVI.m_dmem_wstrb,
			wdata: nerv_BVI.m_dmem_wdata};
   endmethod
   
   method Action m_dmem_rdata (Bit #(32) xd) = nerv_BVI.m_dmem_rdata (xd);
endmodule

// ================================================================

endpackage
