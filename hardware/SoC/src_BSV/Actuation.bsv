package Actuation;

// Actuation interface
interface Actuation_IFC;
    interface ActuationD0_IFC d0;
    interface ActuationD1_IFC d1;
endinterface

interface ActuationD0_IFC;
    (* always_ready *)
    method Bool actuate_d0 (Bit #(96) trips, Bool old);
endinterface

interface ActuationD1_IFC;
    (* always_ready *)
    method Bool actuate_d1 (Bit #(96) trips, Bool old);
endinterface

endpackage