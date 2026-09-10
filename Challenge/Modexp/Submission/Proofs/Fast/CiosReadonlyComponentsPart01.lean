import Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open WindowNibbleKernel CiosCachedMacCore CiosCached CiosCachedMidDefs
open Monpro
open CiosEndAroundCarry

def cacheStack (bi pbi pa pb flag target2 tl inv m0 aEnd m96 m64 m32 dst ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  baseStack bi pbi pa pb flag target2 inv (m0 :: tl :: m96 :: m64 :: m32 :: aEnd :: dst :: ret :: rest)

end Challenge.Modexp.Submission.Proofs.Fast.CiosReadonly
