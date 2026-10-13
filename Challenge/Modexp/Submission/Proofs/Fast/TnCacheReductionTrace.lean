import Challenge.Modexp.Submission.Proofs.Fast.TnCacheL2Chain
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowTrace
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareModel

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheReductionTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached CiosCachedMacCore
open CiosReadonly CiosCachedMidMemory

def dispatch : List Instr := [.op (.Dup ⟨9, by decide⟩), .op .JUMP]

def program (n : Nat) : List Instr :=
  ((TnCacheRowTrace.middle ++ dispatch) ++ TnCacheL2Chain.fullProgram n) ++
    TnCacheRowTrace.tailShort

end Challenge.Modexp.Submission.Proofs.Fast.TnCacheReductionTrace
