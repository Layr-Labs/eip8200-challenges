import Challenge.BytecodeProof.Bytecode
import Challenge.BytecodeProof.Execution
import Challenge.BytecodeProof.Gas
import Challenge.BytecodeProof.Memory
import Challenge.BytecodeProof.Ops
import Challenge.BytecodeProof.Program
import Challenge.BytecodeProof.Word
set_option warningAsError true
/-!
# Direct-bytecode proof support

Infrastructure for proofs that start from participant-supplied EVM bytecode:
a byte-preserving verified disassembler and direct `Step`/`Eval` proof
combinators. This layer has no source-language or compiler-correctness premise.
-/
