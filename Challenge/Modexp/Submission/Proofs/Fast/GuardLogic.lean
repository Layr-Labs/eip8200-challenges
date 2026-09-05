import Challenge.Modexp.Submission.Proofs.Fast.GuardData
import Challenge.EvmProof.Word
import Batteries.Data.Nat.Bitwise.Lemmas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardLogic

open EvmSemantics
open EvmSemantics.EVM
open GuardData

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

/-- Sequential accumulator used by the bytecode's twenty comparisons. -/
def scanDiff (input : ByteArray) : List (Nat × UInt256) → UInt256 → UInt256
  | [], acc => acc
  | p :: ps, acc =>
      scanDiff input ps (UInt256.lor
        (UInt256.xor (MachineState.readWord input p.1) p.2) acc)

def guardDiff (input : ByteArray) : UInt256 :=
  scanDiff input checks
    (UInt256.lor
      (UInt256.xor (UInt256.ofNat input.size) (UInt256.ofNat 611)) 0)

def Matches (input : ByteArray) : Prop :=
  input.size = 611 ∧
    ∀ p, p ∈ checks → MachineState.readWord input p.1 = p.2

private theorem scanDiff_eq_zero_iff (input : ByteArray)
    (xs : List (Nat × UInt256)) (acc : UInt256) :
    scanDiff input xs acc = 0 ↔
      acc = 0 ∧ ∀ p, p ∈ xs → MachineState.readWord input p.1 = p.2 := by
  induction xs generalizing acc with
  | nil => simp [scanDiff]
  | cons p ps ih =>
      rw [scanDiff, ih]
      simp only [wordOr_eq_zero_iff, wordXor_eq_zero_iff,
        List.mem_cons, forall_eq_or_imp]
      aesop

theorem guardDiff_eq_zero_iff (input : ByteArray) (hbound : input.size < 2 ^ 256) :
    guardDiff input = 0 ↔ Matches input := by
  rw [guardDiff, scanDiff_eq_zero_iff]
  simp only [wordOr_eq_zero_iff, wordXor_eq_zero_iff, and_true, Matches]
  constructor
  · rintro ⟨hsize, hwords⟩
    constructor
    · have := congrArg UInt256.toNat hsize
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt hbound] at this
      norm_num at this ⊢
      exact this
    · exact hwords
  · rintro ⟨hsize, hwords⟩
    constructor
    · rw [hsize]
    · exact hwords

end Challenge.Modexp.Submission.Proofs.Fast.GuardLogic
