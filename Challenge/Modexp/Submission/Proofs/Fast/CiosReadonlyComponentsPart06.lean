import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart05

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def cachedLoadLow : List Instr := [.op (.Dup ⟨10, by decide⟩), .op .MLOAD]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
