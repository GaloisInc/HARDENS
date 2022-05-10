<!--SUBSYSTEM RTS Implementation Artifacts-->
## <a id ="rts-implementation-artifacts"></a>RTS Implementation Artifacts (Artifacts)
component Cryptol System Specification (CryptolSpec) A specification of a model written in the Cryptol domain-specific language (DSL), either as Literate Cryptol, which can be Cryptol embedded in Markdown or LaTeX, or plain Cryptol. Cryptol is a strongly typed, functional DSL for specifying and reasoning about bit-level algorithms and their correctness properties and is mainly used to specify cryptographic algorithms. See https://crypto.net/ for more information.

<!--COMPONENT-->
### <a id ="cryptol-software-compiler"></a>Cryptol Software Compiler (CryptolToC)
Multiple versions of a Cryptol software compiler exist which can compile different subsets of the Cryptol language into implementations and test benches written in the C, Java, and LLVM languages.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="cryptol-hardware-compiler"></a>Cryptol Hardware Compiler (CryptolToSystemVerilog)
Multiple versions of a Cryptol hardware compiler exist which can compile different subsets of the Cryptol language into implementations and test benches written in the VHDL, Verilog, and SystemVerilog.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="software-implementation"></a>Software Implementation (Software)
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="hand-written-software-implementation"></a>Hand-written Software Implementation (SWImpl)
inherit Hand-written Software @todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="synthesized-software-implementation"></a>Synthesized Software Implementation (SynthSW)
inherit Machine-generated Software @todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="hardware-implementation"></a>Hardware Implementation (Hardware)
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="hand-written-hardware-implementation"></a>Hand-written Hardware Implementation (HWImpl)
inherit Hand-written Hardware @todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="synthesized-hardware-implementation"></a>Synthesized Hardware Implementation (SynthHW)
inherit Machine-generated Hardware @todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="cots-high-assurance-rv32i-risc-v-cpu"></a>COTS High-Assurance RV32I RISC-V CPU (CPU)
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="compcert-compiler"></a>CompCert Compiler (CompCert)
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="bluespec-compiler"></a>Bluespec Compiler (BSC)
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="symbiflow-synthesizer"></a>SymbiFlow Synthesizer (SymbiFlow)
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="software-binaries"></a>Software Binaries (Binaries)
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="demonstrator-verilog"></a>Demonstrator Verilog (RTL)
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--COMPONENT-->
### <a id ="fpga-bitstream"></a>FPGA Bitstream (Bitstream)
@todo kiniry Add an explanation.
<!--COMPONENT/-->
<!--SUBSYSTEM RTS Implementation Artifacts/-->
<!--SUBSYSTEM Dataflow of RTS Implementation Artifacts-->
## <a id ="dataflow-of-rts-implementation-artifacts"></a>Dataflow of RTS Implementation Artifacts (Dataflow)
This specification, which comes from the Galois HARDENS proposal, describes the relationships between various levels of specifications, implementations, and assurance artifacts for the HARDENS demonstrator. indexing proposal_figure: 3 figure_name: Dataflow of RTS Implementation Artifacts.

<!--RELATION-->
#### relation CryptolToC
* client of [CryptolSpec](#cryptolspec)
<!--RELATION/-->
<!--RELATION-->
#### relation CryptolToSystemVerilog
* client of [CryptolSpec](#cryptolspec)
<!--RELATION/-->
<!--RELATION-->
#### relation SynthSW
* client of [CryptolToC](#cryptoltoc)
<!--RELATION/-->
<!--RELATION-->
#### relation SynthHW
* client of [CryptolToSystemVerilog](#cryptoltosystemverilog)
<!--RELATION/-->
<!--RELATION-->
#### relation SynthHW
* client of [BSC](#bsc)
<!--RELATION/-->
<!--RELATION-->
#### relation CompCert
* client of [SynthSoftImpl](#synthsoftimpl)
<!--RELATION/-->
<!--RELATION-->
#### relation CompCert
* client of [SoftImpl](#softimpl)
<!--RELATION/-->
<!--RELATION-->
#### relation BSC
* inherits [Compiler](#compiler)
<!--RELATION/-->
<!--RELATION-->
#### relation BSC
* client of [HWImpl](#hwimpl)
<!--RELATION/-->
<!--RELATION-->
#### relation SymbiFlow
* client of [SynthHW](#synthhw)
<!--RELATION/-->
<!--RELATION-->
#### relation SymbiFlow
* client of [CPU](#cpu)
<!--RELATION/-->
<!--RELATION-->
#### relation Binaries
* client of [CompCert](#compcert)
<!--RELATION/-->
<!--RELATION-->
#### relation RTL
* client of [SymbiFLow](#symbiflow)
<!--RELATION/-->
<!--RELATION-->
#### relation RTL
* contains [Soft-core RISC-V CPU](#soft-core-risc-v-cpu)
<!--RELATION/-->
<!--RELATION-->
#### relation Bitstream
* contains [SynthHW](#synthhw)
<!--RELATION/-->
<!--RELATION-->
#### relation Bitstream
* contains [CPU](#cpu)
<!--RELATION/-->
<!--RELATION-->
#### relation BitStream
* client of [SymbiFlow](#symbiflow)
<!--RELATION/-->
<!--SUBSYSTEM Dataflow of RTS Implementation Artifacts/-->
