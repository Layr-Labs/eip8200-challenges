import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart06

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def cachedMakeMu : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨10, by decide⟩), .op .MUL,
   .op (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
