# HARDENS Assurance Case

This document outlines the HARDENS assurance case for the Reactor Trip
System (RTS).

## High-Level Specification and Requirements

A domain model, high-level specification of the system, and
requirements are provided via Lando, SysMLv2 architecture diagrams,
and FRET requirements as indicated in the
[readme](./README.md).  Moreover, we use Lando to outline a set of high
level _scenarios_, which are a complete set of behavior traces for
normal and exceptional system behavior.

We build confidence in the correctness of the requirements by
utilizing FRET's realizability checker, which verifies that for a set
of input values satisfying the requirements, a set of _output_ values
exists that satisfy the requirements.  Dually, the tool identifies
inputs for which no output is feasible, which helps to narrow down
subsets of requirements that are inconsistent.

## Executable behavioral specification

Next, refining both the architecture (i.e., SysMLv2) and requirements
(Lando and FRET), we specify the RTS using Cryptol, yielding an
executable _model_ of the system that can be used to further refine
the implementation: for example, it is here that we fully specify the
behavior of the self test function of the RTS.

### Correctness of the refinement step

To build assurance that this model is correct, we write theorems, or
_properties_, in the Cryptol language about the model itself.  Each
and every FRET requirement is translated into a theorem expressing the
fact that the model satisfies the requirement: for example, if a FRET
requirement says that an actuation unit should actuate a device based
on a combination of trip signals, then the Cryptol theorem states the
analogous property about the Cryptol model.

These properties can be proven correct for _all_ inputs in most cases.
Automatic, random testing is performed for the very limited number of
cases where the property is too complex for automatic theorem provers.

Proving requirements-expressed-as-theorems about our formal Cryptol
model is the strongest means by which to perform model validatoin, as
doing so guarantees that we have the _right_ model of the system, and
the model is logically consistent. 

Based upon our experience with Cryptol, we focus on writing a
model-based specification that is both _executable_ and _denotational_
and well-shaped for implementation verification.  Shaping a formal
model thusly gives us confidence that the model is _realizable_, and
thus scan be implemented efficiently in software and hardware.
This evidence bolsters the earlier realizability analysis of the
system requirements, reaffirming those assurance results on the
refined model.

## Implementation Correctness

To build assurance that the RTS implementation is correct (i.e.,
correctly refines the executable model, satisfies the requirements,
etc.), we demonstrate three complementary strategies:

 1. Correct-by-construction generation of components directly from the
    Cryptol model, and then utilizing the SAW tool to further
    guarantee that the generated components are, in fact, correct
    through formal verification.
 2. Formal static verification of the C source code to (1) formally
    prove functional correctness relative to the Cryptol model, and
    (2) guarantee the absence of any runtime errors (e.g., due to
    array out-of-bounds errors).
 3. Traditional runtime verification (i.e., testing), but leaning
    heavily on automatic model-based test generation.

### Component generation

We generate both C and SystemVerilog implementations of key
functions/features directly from the Cryptol model.  For each such
function, we use SAW to prove that the generated component exactly
matches its specification.  It is worth mentioning here that this is
not limited to unit/component-level verification of C functions or
SystemVerilog modules.  This approach also support integration and
system assurance.  For example, the self-test functionality executes a
series of integration and system test cases mechnically extracted
directly from the Cryptol model.

In particular, for C implementations, we use SAW to prove correctness
between the Cryptol model and the LLVM bitcode.  For SystemVerilog
implementations, we use SAW to extract a Verilog module from the
Cryptol specification, and then use the Yosys tool to prove
equivalence between the extracted Verilog module and the generated or
hand-written SystemVerilog module.

Not only does this establish the functional correctness of the
component in question, but writing such specification (that can be
precisely checked) ensures that the interface between components is
made precise.  For example, the final specification must take into
account any differences in endianness assumptions between the source
(Cryptol) and the target (e.g., the Verilog hardware design).

Note that for some of these components, the RTS implementation
includes handwritten versions.  We employ precisely the same
methodology to verify their correctness (and found real bugs in
development).

Recall that the point of including these hand-written implementations
is threefold:

 1. 

### Static verification

We use ACSL to model key components from the Cryptol model. The model is
provided [here](src/include/models.acsl), and is effectively a transliteration
of the Cryptol specification, making the refinement step from Cryptol to ACSL
(close to) obvious. Next, we use this model to specify ACSL contracts inline with the C
code (.e.g `Is_Ch_Tripped` in
[instrumentation.h](src/include/instrumentation.h).

We then use Frama-C and its `wp` plugin to statically verify that such functions
satisfy their contracts, guaranteeing that the implementation refines the
Cryptol model. We use this plugin to additionally verify that the specification
is _consistent_.

Moreover, we use Frama-C's `rte` plugin to further prove the absence of runtime
errors due to undefined behaviors.

### Runtime verification

Finally, we translate each Lando test scenario is translated into an end-to-end
test. Connecting each test to a high level scenario ensures that all high level
behaviors are covered by testing. Testing is complementary to the static
verification above by ensuring that components that can _not_ be verified behave
correctly.
