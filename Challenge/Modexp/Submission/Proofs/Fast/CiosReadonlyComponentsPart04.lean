import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyComponentsPart03

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def dropCache : List Instr := [.op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP, .op .POP]

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
