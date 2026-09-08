import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneSumsLow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneSumsHigh
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore

theorem normalize_ofNat (lo hi : Nat)
    (hlo : lo < 2 ^ 128) (hhi : hi < 2 ^ 128) :
    normalize (BitVec.ofNat 256 (lo + hi * 2 ^ 128)) =
      pack (BitVec.ofNat 32 lo) (BitVec.ofNat 32 hi) := by
  have hcomm : lo + hi * 2 ^ 128 = lo + 2 ^ 128 * hi :=
    congrArg (fun n => lo + n) (Nat.mul_comm hi (2 ^ 128))
  calc
    normalize (BitVec.ofNat 256 (lo + hi * 2 ^ 128)) =
        normalize (BitVec.ofNat 256 (lo + 2 ^ 128 * hi)) :=
      congrArg (fun n => normalize (BitVec.ofNat 256 n)) hcomm
    _ = pack (BitVec.ofNat 32 lo) (BitVec.ofNat 32 hi) :=
      congr (congrArg pack (low_ofNat_pair lo hi hlo hhi))
        (high_ofNat_pair lo hi hlo hhi)

#print axioms normalize_ofNat
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCore
