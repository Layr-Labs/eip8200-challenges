import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80SumsLow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80SumsHigh
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Core

theorem normalize_ofNat (lo hi : Nat)
    (hlo : lo < 2 ^ 80) (hhi : hi < 2 ^ 80) :
    normalize (BitVec.ofNat 256 (lo + hi * 2 ^ 80)) =
      pack (BitVec.ofNat 32 lo) (BitVec.ofNat 32 hi) := by
  have hcomm : lo + hi * 2 ^ 80 = lo + 2 ^ 80 * hi :=
    congrArg (fun n => lo + n) (Nat.mul_comm hi (2 ^ 80))
  calc
    normalize (BitVec.ofNat 256 (lo + hi * 2 ^ 80)) =
        normalize (BitVec.ofNat 256 (lo + 2 ^ 80 * hi)) :=
      congrArg (fun n => normalize (BitVec.ofNat 256 n)) hcomm
    _ = pack (BitVec.ofNat 32 lo) (BitVec.ofNat 32 hi) :=
      congr (congrArg pack (low_ofNat_pair lo hi hlo hhi))
        (high_ofNat_pair lo hi hlo hhi)

#print axioms normalize_ofNat
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Core
