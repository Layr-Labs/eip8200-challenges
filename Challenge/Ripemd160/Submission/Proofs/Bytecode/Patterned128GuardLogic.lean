import Challenge.EvmProof.Word
import EvmSemantics.EVM.Step
import Batteries.Data.Nat.Bitwise.Lemmas

set_option warningAsError true
set_option maxHeartbeats 2000000

/-! Zero/nonzero guard facts adapted from the promoted MODEXP WindowGuardLogic
proof. Kept in this track so correctness does not depend on another editable track. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128GuardLogic
open EvmSemantics EvmSemantics.EVM

private theorem natOr_eq_zero_iff (a b : Nat) :
    a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hbit (i : Nat) :
        a.testBit i = false ∧ b.testBit i = false := by
      have := congrArg (fun n => n.testBit i) h
      simpa using this
    constructor
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).1
    · apply Nat.eq_of_testBit_eq
      intro i
      simpa using (hbit i).2
  · rintro ⟨rfl, rfl⟩
    decide

theorem wordOr_eq_zero_iff (a b : UInt256) :
    UInt256.lor a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hzeroNat : (0 : UInt256).toNat = 0 := by decide
    have hnat : a.toNat ||| b.toNat = 0 := by
      rw [← Challenge.EvmProof.Word.word_toNat_lor, h]
      rfl
    rcases (natOr_eq_zero_iff a.toNat b.toNat).1 hnat with ⟨ha, hb⟩
    constructor
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact ha
    · apply Challenge.EvmProof.Word.word_ext
      rw [hzeroNat]
      exact hb
  · rintro ⟨rfl, rfl⟩
    decide

private theorem word_toNat_xor (a b : UInt256) :
    (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  change (a.val ^^^ b.val).val = _
  rw [Fin.xor_val]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_lt_of_le
    (Nat.xor_lt_two_pow a.val.isLt b.val.isLt) (by rfl)

theorem wordXor_eq_zero_iff (a b : UInt256) :
    UInt256.xor a b = 0 ↔ a = b := by
  constructor
  · intro h
    apply Challenge.EvmProof.Word.word_ext
    apply Nat.eq_of_xor_eq_zero
    rw [← word_toNat_xor, h]
    rfl
  · rintro rfl
    apply Challenge.EvmProof.Word.word_ext
    rw [word_toNat_xor, Nat.xor_self]
    rfl


theorem ofNat_eq_iff {a b : Nat} (ha : a < 2^256) (hb : b < 2^256) :
    UInt256.ofNat a = UInt256.ofNat b ↔ a = b := by
  constructor
  · intro h
    have hn := congrArg UInt256.toNat h
    simpa only [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hn
  · rintro rfl; rfl

theorem isTrue_of_ne_zero (x : UInt256) (hx : x ≠ 0) : UInt256.isTrue x := by
  unfold UInt256.isTrue
  intro hz
  apply hx
  apply Challenge.EvmProof.Word.word_ext
  change x.toNat = 0
  exact hz

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128GuardLogic
