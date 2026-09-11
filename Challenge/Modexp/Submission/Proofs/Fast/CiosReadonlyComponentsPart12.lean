import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart11

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def makeModProduct : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨13, by decide⟩), .op .MULMOD]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
