import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Sums

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Message

open Paired80Core

/-- Table reads may contain arbitrary extra bits above the two message lanes. -/
def Eq112 (x y : BitVec 256) : Prop := x.toNat % 2 ^ 112 = y.toNat % 2 ^ 112

theorem normalize_congr (x y : BitVec 256) (h : Eq112 x y) :
    normalize x = normalize y := by
  have hl : low x = low y := by
    apply BitVec.eq_of_toNat_eq
    simp only [low, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
    unfold Eq112 at h
    simp only [Nat.reducePow] at *
    omega
  have hh : high x = high y := by
    apply BitVec.eq_of_toNat_eq
    simp only [high, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    unfold Eq112 at h
    simp only [Nat.reducePow] at *
    omega
  simp only [normalize, hl, hh]

theorem add_right (x y z : BitVec 256) (h : Eq112 x y) :
    Eq112 (x + z) (y + z) := by
  unfold Eq112 at *
  simp only [BitVec.toNat_add, Nat.reducePow] at *
  omega

theorem add_left (x y z : BitVec 256) (h : Eq112 x y) :
    Eq112 (z + x) (z + y) := by
  simpa only [BitVec.add_comm z] using add_right x y z h

theorem normalize_add_message (before after x y : BitVec 256) (h : Eq112 x y) :
    normalize ((before + x) + after) = normalize ((before + y) + after) :=
  normalize_congr _ _ (add_right _ _ after (add_left x y before h))

#print axioms normalize_congr
#print axioms add_right
#print axioms normalize_add_message

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired80Message
