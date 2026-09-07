import Challenge.Modexp.Spec
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Batteries.Data.Nat.Bitwise.Lemmas

set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# Fixed-width route guard

Pure semantics of the three-word width guard at pc 3000.  Keeping this lemma
independent of the generated artifact lets the execution proof reduce the
branch condition without importing any of the window arithmetic.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic

open EvmSemantics
open EvmSemantics.EVM

/-- The exact declared-width predicate tested by the appended route. -/
def Matches (input : ByteArray) : Prop :=
  baseSize input = 32 ∧ exponentSize input = 32 ∧ modulusSize input = 32

/-- The accumulated XOR/OR value immediately before the route's `ISZERO`. -/
def guardDiff (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.xor (UInt256.ofNat (modulusSize input)) (UInt256.ofNat 32))
    (UInt256.lor
      (UInt256.xor (UInt256.ofNat (exponentSize input)) (UInt256.ofNat 32))
      (UInt256.xor (UInt256.ofNat (baseSize input)) (UInt256.ofNat 32)))

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

private theorem ofNat_eq_32_iff {n : Nat} (hn : n < 2 ^ 256) :
    UInt256.ofNat n = UInt256.ofNat 32 ↔ n = 32 := by
  constructor
  · intro h
    have hnat := congrArg UInt256.toNat h
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hn,
      Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)] at hnat
    exact hnat
  · rintro rfl
    rfl

private theorem pow_256_32 : (256 : Nat) ^ 32 = 2 ^ 256 := by
  norm_num

private theorem headerSize_lt (input : ByteArray) (offset : Nat) :
    Precompile.bytesToNatPadded input offset 32 < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset 32
  rw [pow_256_32] at h
  exact h

theorem guardDiff_eq_zero_iff (input : ByteArray) :
    guardDiff input = 0 ↔ Matches input := by
  have hb : baseSize input < 2 ^ 256 := headerSize_lt input 0
  have he : exponentSize input < 2 ^ 256 := headerSize_lt input 32
  have hm : modulusSize input < 2 ^ 256 := headerSize_lt input 64
  simp only [guardDiff, wordOr_eq_zero_iff, wordXor_eq_zero_iff, Matches]
  rw [ofNat_eq_32_iff hm, ofNat_eq_32_iff he, ofNat_eq_32_iff hb]
  constructor <;> rintro ⟨hm, he, hb⟩ <;> exact ⟨hb, he, hm⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
