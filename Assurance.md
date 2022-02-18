# HARDENS Assurance Case

*Alex Bakst and Joe Kiniry, February 2022*

This document outlines the HARDENS assurance case for the Reactor Trip
System (RTS), which has been designed, developed, and assured using
Galois's Rigorous Digital Engineering (RDE) approach to high-assurance
engineering.

## RTS Digital Twins

Our assurance case spans from high-level system specification, in
natural language documentation, like this document, and the Lando
specification that looks and tastes like English, to the software and
hardware binary level.  In between high-level specifications and
our lowest level, closest to the hardware implementation (in the case
of HARDENS, C source code compiled to RISC-V binaries using Clang
running on on a custom HARDENS three-core RISC-V SoC  implemented as
softcore IP synthesized to and running on a COTS Lattice FPGA) are a
variety of **Rigorous Digital Twins**.

**Digital Twins** are executable versions of a system for which
various physical components of the "real" system are replaced by
digital representations.

For example, our three core SoC running on an FPGA is a digital twin
of (1) the same three core SoC implemented as an ASIC, (2) three
single core SoCs running on an FPGA, or (3) three single core SoCs
running on three FPGAs connected via an AXI bus, or (4) three single
core ASICs connected on an AXI bus.

The digital twins that we have built for HARDENS are:
 1. A build and simulation of the entire software stack which runs on
    POSIX OSs like Linux and macOS.
 2. A build of the software stack targeting the single core variant of
    our RISC-V-based SoC, running via RTL software simulation in
    Verilator.
 3. A build of the software stack targeting the three core variant of
    our RISC-V-based SoC, running via RTL software simulation in
    Verilator.
 4. Our executable Cryptol model which faithfully specify and
    implements all system behavior.

Other twins are possible with our current infrastructure, including
running our Bluespec-based SoC entirely within the Bluespec event
simulator, emulating our SoC inside of other non-Verilator RTL
simulators, or completing a full behavioral model of the system in
SysMLv2 and executing that model in a commercial modeling tool, at
least when such functionality comes into being.

Likewise, there is a possibility to mix and match twins at the
component and subsystem level, rather than just at the system level.
This is not implemented in the current demonstrator, but adding
support for such is a matter of engineering, not research.

For example, it is wholly possible to run our executable models of
sensors and actuators on the FPGA-based demonstrator, whether or not
the actual physical sensors and actuators are attached.  In fact, we
do simulate such devices as digital twins in our test bench in order
to automatically demonstrate the RTS system's resilience to component
and communication failure.

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

## Executable Behavioral Specification

Next, refining both the architecture (i.e., SysMLv2) and requirements
(Lando and FRET), we specify the RTS using Cryptol, yielding an
executable _model_ of the system that can be used to further refine
the implementation: for example, it is here that we fully specify the
behavior of the self test function of the RTS.

## Correctness of Refinements

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
model is the strongest means by which to perform model validation, as
doing so guarantees that we have the _right_ model of the system, and
the model is logically consistent. 

Based upon our experience with Cryptol, we focus on writing a
model-based specification that is both _executable_ and _denotational_
and well-shaped for implementation verification.  Shaping a formal
model in this fashion gives us confidence that the model is
_realizable_, and thus scan be implemented efficiently in software and
hardware.  This evidence bolsters the earlier realizability analysis
of the system requirements, reaffirming those assurance results on the
refined model.

## Digital Twin and Implementation Correctness

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

## Component Generation

We generate both C and SystemVerilog implementations of key
functions/features directly from the Cryptol model.  For each such
function, we use SAW to prove that the generated component exactly
matches its specification.  It is worth mentioning here that this is
not limited to unit/component-level verification of C functions or
SystemVerilog modules.  This approach also support integration and
system assurance.  For example, the self-test functionality executes a
series of integration and system test cases technically extracted
directly from the Cryptol model.

## Runtime Verification

We translate each Lando scenario into either a subsystem level
integration test or an end-to-end system test.  Traceably connecting
each test to a high level scenario ensures that all high level
behaviors are covered by testing.

In general, testing is complementary to the static verification and
formal verification discussed below because testing provides extra
evidence that a verified component is correct and testing demonstrates
correctness for those components that **cannot** be formally verified.

There are two additional reasons to rigorously validate a system
through runtime verification:

 1. Some customers do not understand, cannot accept, cannot use, or do
    not trust formal assurance in the form of mathematical/logical
    proof.  Proving that an implementation conforms perfectly to its
    specification, for all inputs and all environments, is a foreign
    notion.  These kinds of customers are much more comfortable with
    executing a system and running a traditional testing-based
    verification plan on a product.
 2. Only runtime verification can demonstrate the real deployment
    software running on the actual deployment hardware.  All of the
    verification in the world cannot capture the reality and fidelity
    of the actual deployment silicon on which a system runs.

## Runtime Verification with Digital Twins

In the world of RDE, different kinds of digital twins have different
degrees of fidelity when compared to the deployment system.  This is
partly the reason that we write, generate, and run runtime
verification test benches on all digital twins.

For example, all things being equal, cleanly written verifiable C [1]
code should run identically on any POSIX-based operating system,
regardless of the flavor of OS (Linux, BSD, macOS, what have you) and
which CPU sits underneath that OS (ARM, x86, RISC-V, etc.).  (By
"verifiable C" we mean the subset of C for which there is a
well-defined semantics, as supported by various formal reasoning tools
and technologies that we use like Frama-C, SAW, VST, and CompCert.)

Likewise, simulating a SoC written in an HDL can be performed at at
least four different fidelity levels, and consequently with four
different levels of simulation performance.  The RTL can be simulated
in: (1) an event-based simulator that does not guarantee
cycle-accurate behavior (e.g., Verilator, Yosys's CXXRTL, or the
Metrics Design Automation RTL simulator), (2) a cycle-accurate event
simulator (e.g., Berkeley's FireSim, which we have used on other
projects but not on HARDENS), (3) a cycle-accurate digital circuit
simulator (such as supported by many commercial simulators), or (4) a
cycle-accurate physics-based hardware simulator (such as LTspice or
Xyce).

Moreover, for even higher performance, and lower fidelity, simulation
is possible using purely software functional behavioral models such as
those implemented in SystemC (our favorite flavor comes from Imperas)
in architecture modeling frameworks (like Gem5), or in system
emulators (such as QEMU).  While we do not use any of these digital
twin options in HARDENS, we have used all of them in other RDE-centric
R&D at Galois.

## Static Verification

We use ACSL to model key components from the Cryptol model. The model
is provided [here](src/include/models.acsl), and is effectively a
transliteration of the Cryptol specification, making the refinement
step from Cryptol to ACSL (close to) obvious.  Next, we use this model
to specify ACSL contracts inline with the C code (e.g.,
`Is_Ch_Tripped` in [instrumentation.h](src/include/instrumentation.h).

We then use Frama-C and its `wp` plugin to statically verify that such
functions satisfy their contracts, guaranteeing that the
implementation refines the Cryptol model.  We use this plugin to
additionally verify that the specification is _consistent_.

Moreover, we use Frama-C's `rte` plugin to further prove the absence
of runtime errors due to undefined behaviors.  The undefined behaviors
that such analysis helps us avoid/prevent are all those that sit at
the core of unsafe languages like C, including invalid pointer
dereference errors, arithmetic overflow errors, division by zero
errors, etc.  In general, the errors that this kind of analysis can
find either relate to exceptional behavior triggered by erroneous code
or behavior that is undefined in the C programming language.

## Formal Verification

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

## Duplicated Component Correctness for Safety-Engineering

Note that for some of these components, the RTS implementation
includes handwritten versions.  We employ precisely the same
methodology to verify their correctness (and found real bugs in
development).

Recall that the point of including these hand-written implementations
is threefold:

 1. Since the RTS is a safety-critical system, key
    subsystems/components are duplicated and the architecture is fault
    tolerant.  One mechanism used to have high-assurance of such
    duplicate functionality is to independently implement the various
    components that are used in the fault-tolerant subsystem.
    
    It has been historically proposed that even higher-assurance would
    result in a systems engineering process that can prove that such
    implementation are equivalent, so long as one can also formally
    prove that their specifications are correct against more abstract
    requirements and/or specification, otherwise all implementations
    might exactly implement erroneous functionality.  This is exactly
    what we have achieved in the RTS, and to our knowledge, this is
    the first time this has ever been demonstrated on a system whose
    assurance case spans software, firmware, and hardware-based
    fault-tolerance duplication.
    
 2. Virtually all code in the field is hand-written and is reused,
    thus we wanted to demonstrate that our RDE methodology can
    accommodate such code.  In particular, it is important to
    demonstrate how formal models can be used to assure what might
    otherwise be considered untrustworthy reused components, either
    through runtime verification, formal verification, or both.  Our
    use of SAW, Frama-C, and model-based runtime verification of
    hand-written components is well-beyond the state-of-the-art in
    nearly all safety-critical model-based systems engineering, and is
    representative of what model-based engineering can and must
    accomplish for safety-critical systems in NPPs like RTSs.
    
 3. Some teams and customers are uncomfortable with using
    implementation that are automatically generated or synthesized
    from formal methods.  They prefer to write, use, maintain,
    optimize, and evolve hand-written implementations.
    
    For these kinds of situations, we recommend that automatically
    generated implementations are used as _assurance artifacts_,
    rather than _deployment artifacts_.  Our RDE methodology in this
    project demonstrates how one can rigorously validate or formally
    verify a hand-written component against a golden implementation
    model, which is the generated implementation.
    
    Rigorous validation is demonstrable and measurable by using the
    automatically generated test suite to runtime verify (1) the
    executable model, (2) the golden implementation model, and (3) the
    hand-written implementation of the model.  All three executable
    artifacts must pass all tests in exactly the same fashion, when
    running within all digital twins of the project.
    
## Quality Metrics for Verification
    
In order to judge whether or not such multi-dimensional runtime
verification is meaningful, we need a measure of quality for the
model(s) and test suite(s).  We traditionally use three core measures,
some of which are partially (due to project budget and scope, not
assurance capability) demonstrated in the RTS system.
    
First, we measure _model quality_ through the previously discussed
methodology of refining requirements and system scenarios into model
theorems.  By proving or demonstrating that the model conforms to the
requirements, scenarios, and theorems, we know that the model is
valid, consistent, realizable, and sound.  Additionally, we can
instrument the model to discover if there are any model components
that are not exercised, either via proof or testing, by the full model
assurance case.
    
Second, model theorems are translated into implementation properties,
expressed as parametrized first-order test cases.  Then we use
property-based testing **and** formal verification against said
properties to demonstrate that the implementation perfectly fulfills
system requirements and scenarios.

Finally, third, we can measure source-level and binary-level code
runtime verification coverage of the system.  In general, our RDE
methodology guarantees extremely high statement, block, function,
function call, branch, and condition/decision coverage of the entire
modeled system.  It is commonly the case that we achieve >98% coverage
"out of the box", and then use either program analysis or subject
matter expert review to automatically generate or hand-write the
remaining <2% of unit, integration, or system test cases.  This
methodology means that we need only manage, evolve, and maintain two
orders of magnitude fewer test cases than a traditional agile or
test-centric development process.

Moreover, and to bolster the overall assurance case, all source-level
test benches can be compiled and run on all SoC digital twins,
demonstrating that the system passes **all** runtime verification
assurance tests for **all** digital variants of the system.

