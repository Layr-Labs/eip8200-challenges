import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart07

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def cachedLoadMask : List Instr := [.op (.Dup ⟨8, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
