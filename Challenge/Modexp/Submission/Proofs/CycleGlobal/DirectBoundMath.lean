import Challenge.EvmProof.Word
namespace CycleSubmission.Global.DirectBoundMath
open EvmSemantics Challenge.EvmProof.Word
set_option maxHeartbeats 1000000

theorem guard_eq (w : UInt256) :
    UInt256.lt (UInt256.ofNat (2^256 - 2^146 - 1)) w =
      UInt256.isZero (UInt256.shiftRight (UInt256.lnot w) (UInt256.ofNat 146)) := by
  have hw : w.toNat < 2^256 := w.val.isLt
  have hlnot : (UInt256.lnot w).toNat = 2^256 - 1 - w.toNat := by
    rw [UInt256.lnot, word_toNat_ofNat]
    change (2^256 - 1 - w.toNat) % 2^256 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hb : (UInt256.ofNat (2^256 - 2^146 - 1)).toNat = 2^256 - 2^146 - 1 := by
    rw [word_toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
  apply word_ext
  rw [word_toNat_lt, hb, word_toNat_isZero,
    shiftRight_toNat _ (by decide : 146 < 256), Nat.shiftRight_eq_div_pow,
    hlnot]
  have hi : 2^256 - 2^146 - 1 < w.toNat ↔ 2^256 - 1 - w.toNat < 2^146 := by omega
  simp only [Nat.div_eq_zero_iff_lt (by decide : 0 < 2^146), hi]

theorem zero_iff (w : UInt256) :
    (UInt256.shiftRight (UInt256.lnot w) (UInt256.ofNat 146)).toNat = 0 ↔
      2^256-2^146-1 < w.toNat := by
  have hw : w.toNat < 2^256 := w.val.isLt
  have hlnot : (UInt256.lnot w).toNat = 2^256 - 1 - w.toNat := by
    rw [UInt256.lnot, word_toNat_ofNat]
    change (2^256 - 1 - w.toNat) % 2^256 = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [shiftRight_toNat _ (by decide : 146 < 256), Nat.shiftRight_eq_div_pow, hlnot]
  rw [Nat.div_eq_zero_iff_lt (by decide : 0 < 2^146)]
  omega

#print axioms zero_iff
#print axioms guard_eq
end CycleSubmission.Global.DirectBoundMath
