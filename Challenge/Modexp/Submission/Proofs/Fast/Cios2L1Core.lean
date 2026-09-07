import Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

/-- L1 state at an arbitrary copied-body boundary. -/
def l1At (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
                     UInt256.ofNat (ptrAt (8224 + 32 * n) j),
                     (l1Step mem bi pa n j).carry, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32),
                     (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256), pdst, ret] ++ rest
           memory := (l1Step mem bi pa n j).memory }

abbrev l1State := l1At 4171

/-- Row middle reached after the final L1 MAC. -/
def midState (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4732
           stack := [paj, ptj, c, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32),
                     (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256), pdst, ret] ++ rest
           memory := mem }

theorem jumpDest4171 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4171 = true := by
  exact Artifact.isValidJumpDest_index 2729 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
