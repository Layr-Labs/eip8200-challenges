import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.EvmProof.Word

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.EarlyCsub
open EvmSemantics
open Challenge.Modexp.Submission.Proofs
open Challenge.EvmProof.Word

/-- Nonzero exactly when the high-limb test cannot rule out subtraction. -/
def guardWord (mem : ByteArray) : UInt256 :=
  UInt256.lor (MachineState.readWord mem 4128)
    (UInt256.isZero (UInt256.lt (MachineState.readWord mem 4160) (MachineState.readWord mem 0)))

theorem guardWord_eq (mem : ByteArray) : guardWord mem =
    UInt256.lor (MachineState.readWord mem 4128)
      (UInt256.isZero (UInt256.lt (MachineState.readWord mem 4160) (MachineState.readWord mem 0))) := rfl

def Skip (mem : ByteArray) : Prop := (guardWord mem).toNat = 0
instance (mem : ByteArray) : Decidable (Skip mem) := inferInstanceAs (Decidable (_ = 0))

theorem skip_iff (mem : ByteArray) : Skip mem ↔
    (MachineState.readWord mem 4128).toNat = 0 ∧
    (MachineState.readWord mem 4160).toNat < (MachineState.readWord mem 0).toNat := by
  unfold Skip guardWord
  rw [word_toNat_lor, word_toNat_isZero, word_toNat_lt]
  by_cases h : (MachineState.readWord mem 4160).toNat < (MachineState.readWord mem 0).toNat
  · simp [h]
  · simp [h]
    intro hz
    have hb := congrArg (fun k : Nat => k.testBit 0) hz
    simp at hb

/-- For equal-width big-endian arrays, a strict high-limb comparison orders
    the represented integers regardless of all lower limbs. -/
theorem high_limb_lt {mem : ByteArray} {n t m : Nat}
    (hn : 1 ≤ n) (ht : Model.FastRepresents mem 4160 n t)
    (hm : Model.FastRepresents mem 0 n m)
    (h : (MachineState.readWord mem 4160).toNat < (MachineState.readWord mem 0).toNat) :
    t < m := by
  have ht0 := Model.readWord_of_fastRepresents ht (j := 0) (by omega)
  have hm0 := Model.readWord_of_fastRepresents hm (j := 0) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at ht0 hm0
  have hp : Limbs.radix ^ n = Limbs.radix ^ (n-1) * Limbs.radix := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [pow_succ]
  have htq : t / Limbs.radix ^ (n-1) < Limbs.radix := by
    apply (Nat.div_lt_iff_lt_mul (pow_pos Limbs.radix_pos _)).2
    simpa only [hp, Nat.mul_comm] using ht.1
  have hmq : m / Limbs.radix ^ (n-1) < Limbs.radix := by
    apply (Nat.div_lt_iff_lt_mul (pow_pos Limbs.radix_pos _)).2
    simpa only [hp, Nat.mul_comm] using hm.1
  rw [ht0, hm0, Nat.mod_eq_of_lt htq, Nat.mod_eq_of_lt hmq] at h
  by_contra! hnot
  have hdiv := Nat.div_le_div_right (c := Limbs.radix ^ (n-1)) hnot
  omega

end Challenge.Modexp.Submission.Proofs.Fast.EarlyCsub
