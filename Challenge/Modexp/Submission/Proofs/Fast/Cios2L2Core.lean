import Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Peel
import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Mid
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

def tailState (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 5255
           stack := [pmj, ptj, c, mu, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32),
                     (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256), pdst, ret] ++ rest
           memory := mem }

theorem jumpDest4905 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4905 = true := by
  exact Artifact.isValidJumpDest_index 3122 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L2Pair
