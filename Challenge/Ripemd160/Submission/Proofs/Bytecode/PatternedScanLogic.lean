import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedWordLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# What a vanishing accumulator says about the calldata

The scan ors together the differences of thirty-one whole words and of the
padded tail word, so the accumulator vanishes exactly when all thirty-two agree
with the vector; with the size check that pins the calldata to the vector.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedWordData PatternedSwar

/-- Every derived word is the word of the vector. -/
theorem guardWord_eq (j : Nat) (hj : j < 31) : guardWord j = expectedWordAt j := by
  interval_cases j <;> simp

/-- The tail constant, shifted up to meet the zero padding. -/
theorem tailWord_eq :
    UInt256.shiftLeft (0x88add2f71c41668b : UInt256) (192 : UInt256)
      = expectedWordAt 31 := by decide

theorem scanAcc_zero_iff (input : ByteArray) (n : Nat) :
    scanAcc input n = 0 ↔
      ∀ j, j < n → MachineState.readWord input (32 * j) = guardWord j := by
  induction n with
  | zero => exact ⟨fun _ j hj => absurd hj (by omega), fun _ => rfl⟩
  | succ n ih =>
      rw [scanAcc, KnownInputLogic.wordOr_eq_zero_iff,
        KnownInputLogic.wordXor_eq_zero_iff, ih]
      constructor
      · rintro ⟨hprev, hlast⟩ j hj
        by_cases heq : j = n
        · subst j; exact hlast
        · exact hprev j (by omega)
      · intro hall
        exact ⟨fun j hj => hall j (by omega), hall n (by omega)⟩

theorem scanAccFinal_zero_iff_eq (input : ByteArray) (hsize : input.size = 1000) :
    scanAccFinal input = 0 ↔ input = patternedInput := by
  unfold scanAccFinal
  rw [KnownInputLogic.wordOr_eq_zero_iff, KnownInputLogic.wordXor_eq_zero_iff,
    scanAcc_zero_iff]
  constructor
  · rintro ⟨hw, ht⟩
    refine PatternedWordLogic.eq_patternedInput_of_words input hsize (fun j hj => ?_)
    by_cases h31 : j = 31
    · subst j
      rw [show 32 * 31 = 992 from by norm_num, ← ht, tailWord_eq]
    · rw [hw j (by omega), guardWord_eq j (by omega)]
  · rintro rfl
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [PatternedWordLogic.readWord_patterned j, guardWord_eq j (by omega)]
    · rw [tailWord_eq, show (992 : Nat) = 32 * 31 from by norm_num,
        PatternedWordLogic.readWord_patterned 31]

theorem scanAccFinal_patterned : scanAccFinal patternedInput = 0 :=
  (scanAccFinal_zero_iff_eq patternedInput patternedInput_size).2 rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
