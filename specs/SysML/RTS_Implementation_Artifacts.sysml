package <Artifacts> 'RTS Implementation Artifacts' {
  private import ScalarValues::*;
  private import 'Project Glossary'::*;

  // @design Remove concepts in general Glossary that duplicate or
  // overlap with these concepts.  Move abstract items to Glossary.
  part def <CryptolToC> 'Cryptol Software Compiler':> Compiler {
    ref item input: CryptolSpec redefines input;
    ref item output: C_Source redefines output;
  }
  part def <CryptolToSystemVerilog> 'Cryptol Hardware Compiler':> Compiler {
    ref item input: CryptolSpec redefines input;
    ref item output: SystemVerilog redefines output;
  }
  part def <CPU> 'COTS High-Assurance RV32I RISC-V CPU':> CPU, RISC_V_ISA;
  part def <CompCert> 'CompCert Compiler':> Compiler {
    ref item input: C_Source redefines input;
    ref item output: RISCV_Binary redefines output;
  }
  part def <BSC> 'Bluespec Compiler':> Compiler {
    ref item input: BluespecSystemVerilog redefines input;
    ref item output: SystemVerilog redefines output;
  }
  part def <SymbiFlow> 'SymbiFlow Synthesizer' :> Synthesizer {
    ref item input: SystemVerilog redefines input;
    ref item output: Bitstream redefines output;
  }
  part def <RTL> 'Demonstrator Verilog';
  part def 'Demonstrator Bitstream':> Bitstream;
  package <Dataflow> 'Dataflow of RTS Implementation Artifacts' {
    private import 'RTS Implementation Artifacts'::*;

    part def 'HARDENS Cryptol System Specification':> CryptolSpec {
     // :>> literate = true;
    }
    // bind 'HARDENS Cryptol System Specification'.output = CryptolToC.input;
  }
}