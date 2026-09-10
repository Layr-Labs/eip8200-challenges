import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart12

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def finishCarry : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨1, by decide⟩), .op .GT, .op .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
