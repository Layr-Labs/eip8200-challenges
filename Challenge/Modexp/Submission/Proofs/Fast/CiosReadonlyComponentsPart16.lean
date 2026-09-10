import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart15

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def cachedProduct : List Instr :=
  (((cachedLoadLow ++ cachedMakeMu) ++ cachedLoadMask) ++
    makeModProduct) ++ finishCarry

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
