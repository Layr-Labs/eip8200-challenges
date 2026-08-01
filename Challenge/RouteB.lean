import Challenge.RouteB.Bytecode
import Challenge.RouteB.Execution
set_option warningAsError true
/-!
# Route B support

Infrastructure for proofs that start from participant-supplied EVM bytecode:
a byte-preserving verified disassembler and direct `Step`/`Eval` proof
combinators. This layer has no source-language or compiler-correctness premise.
-/
