import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64Anchor
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TerminalXorRaw

set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
# Repeat math under the low-64 screen

`Low64Anchor.low64_anchor` needs the two windows at 960 and 968 in addition to
`SHL 192 (low64 XOR readWord 0) = 0`.  Those windows are already implied by
`TerminalXorRaw.mismatch = 0` once the screen rules out a zero reference word:
the folded accumulator is boolean, so a zero mismatch forces every comparison
in `offsets.dropLast`, including 960, and the seed comparison at 968.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open KnownInputCompactState
open TerminalMulRaw UnrolledRepeatRaw DirectGuard

/-- The on-chain low-64 screen, without the two overlap windows. -/
def condition (input : ByteArray) : UInt256 :=
  UInt256.shiftLeft
    (UInt256.xor (UInt256.ofNat 7016996765293437281) (MachineState.readWord input 0))
    (UInt256.ofNat 192)

private theorem eq_one_iff (w r : UInt256) : UInt256.eq w r = 1 ↔ w = r := by
  unfold UInt256.eq
  split
  · rename_i h
    exact ⟨fun _ => Word.word_ext h, fun _ => rfl⟩
  · rename_i h
    refine ⟨?_, ?_⟩
    · intro h0
      exact absurd h0 (by decide : (0 : UInt256) ≠ 1)
    · intro heq
      exact absurd (congrArg UInt256.toNat heq) h

private theorem isZero_eq_one_iff (a : UInt256) : UInt256.isZero a = 1 ↔ a = 0 := by
  unfold UInt256.isZero
  split
  · rename_i h
    exact ⟨fun _ => Word.word_ext h, fun _ => rfl⟩
  · rename_i h
    refine ⟨?_, ?_⟩
    · intro h0
      exact absurd h0 (by decide : (0 : UInt256) ≠ 1)
    · intro hz
      exact absurd (congrArg UInt256.toNat hz) h

private theorem land_eq_one {a b : UInt256} (ha : BooleanWord a) (hb : BooleanWord b) :
    UInt256.land a b = 1 ↔ a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private theorem foldAcc_eq_one_iff (input : ByteArray) (r a : UInt256) (xs : List Nat)
    (ha : BooleanWord a) :
    foldAcc input r a xs = 1 ↔
      a = 1 ∧ ∀ offset ∈ xs, MachineState.readWord input offset = r := by
  induction xs generalizing a with
  | nil =>
    simp [foldAcc]
  | cons offset rest ih =>
    rw [foldAcc, List.foldl_cons, ← foldAcc]
    have hstep := step_boolean input r a offset ha
    rw [ih _ hstep]
    unfold step
    rw [land_eq_one (eq_boolean _ _) ha, eq_one_iff]
    constructor
    · rintro ⟨⟨hw, ha1⟩, hrest⟩
      refine ⟨ha1, ?_⟩
      intro o ho
      rcases List.mem_cons.mp ho with rfl | ho
      · exact hw
      · exact hrest o ho
    · rintro ⟨ha1, hall⟩
      refine ⟨⟨hall offset (List.mem_cons.mpr (Or.inl rfl)), ha1⟩, ?_⟩
      intro o ho
      exact hall o (List.mem_cons.mpr (Or.inr ho))

private theorem offsets_mem_960 : 960 ∈ offsets.dropLast := by
  unfold offsets
  decide

private theorem reference_ne_zero (input : ByteArray) (hcond : condition input = 0) :
    referenceWord input ≠ 0 := by
  intro hz
  have hshl : UInt256.shiftLeft
      (UInt256.xor (UInt256.ofNat Low64Anchor.low64) (referenceWord input))
      (UInt256.ofNat 192) = 0 := by
    simpa [condition, referenceWord, Low64Anchor.low64] using hcond
  have hmod := Low64Anchor.low64_of_shl (referenceWord input) hshl
  rw [hz] at hmod
  have hzero : (0 : UInt256).toNat = 0 := by
    rw [show (0 : UInt256) = UInt256.ofNat 0 from rfl, Word.word_toNat_ofNat]
    exact Nat.zero_mod _
  simp [hzero, Low64Anchor.B, Nat.zero_mod] at hmod

/-- Under the low-64 screen, a zero terminal mismatch is exactly the repeated
word together with every equality-accumulator comparison. -/
theorem mismatch_zero_iff (input : ByteArray) (hcond : condition input = 0) :
    TerminalXorRaw.mismatch input = 0 ↔
      referenceWord input = KnownInputData.fullWord ∧ equalityAcc input 10 = 1 := by
  constructor
  · intro hm
    have hfoldBool := foldAcc_boolean input (referenceWord input) (equalityAcc input 0)
      offsets.dropLast (equalityAcc0_boolean input)
    have hmul := (KnownInputLogic.wordXor_eq_zero_iff _ _).1 hm
    have hfold : foldAcc input (referenceWord input) (equalityAcc input 0) offsets.dropLast = 1 := by
      rcases hfoldBool with h0 | h1
      · rw [h0, mul_zero] at hmul
        exact absurd hmul.symm (reference_ne_zero input hcond)
      · exact h1
    have hall :=
      (foldAcc_eq_one_iff input (referenceWord input) (equalityAcc input 0) offsets.dropLast
        (equalityAcc0_boolean input)).1 hfold
    have h960 : MachineState.readWord input 960 = MachineState.readWord input 0 := by
      simpa [referenceWord] using hall.2 960 offsets_mem_960
    have h968 : MachineState.readWord input 968 = MachineState.readWord input 0 := by
      have hseed : UInt256.eq (referenceWord input) (MachineState.readWord input 968) = 1 := by
        simpa [equalityAcc] using hall.1
      simpa [referenceWord] using ((eq_one_iff _ _).1 hseed).symm
    have hshl : UInt256.shiftLeft
        (UInt256.xor (UInt256.ofNat Low64Anchor.low64) (MachineState.readWord input 0))
        (UInt256.ofNat 192) = 0 := by
      simpa [condition, Low64Anchor.low64] using hcond
    have hrefWord := Low64Anchor.low64_anchor input h960 h968 hshl
    have href : referenceWord input = KnownInputData.fullWord := by
      simpa [referenceWord] using hrefWord
    have heq : equalityAcc input 10 = 1 := by
      rw [← TerminalXorRaw.isZero_mismatch input href]
      rw [hm]
      exact (isZero_eq_one_iff 0).2 rfl
    exact ⟨href, heq⟩
  · rintro ⟨href, heq⟩
    have hzero : UInt256.isZero (TerminalXorRaw.mismatch input) = 1 := by
      rw [TerminalXorRaw.isZero_mismatch input href, heq]
    exact (isZero_eq_one_iff _).1 hzero

/-- The pinned 1000-byte vector passes the low-64 screen. -/
theorem target_condition : condition KnownInputData.targetInput = 0 := by
  have hread := KnownInputData.targetInput_readWord 0 (by decide : (0 : Nat) < 32)
  unfold condition
  rw [hread]
  simp [KnownInputData.expectedWord]
  decide

theorem mismatch_zero_target (input : ByteArray) (hsize : input.size = 1000)
    (hcond : condition input = 0) (hm : TerminalXorRaw.mismatch input = 0) :
    input = KnownInputData.targetInput := by
  obtain ⟨href, heq⟩ := (mismatch_zero_iff input hcond).1 hm
  have hrev : reverseAcc input 10 = 0 :=
    (isZero_eq_one_iff _).1 (by rw [← equalityAcc_reverse, heq])
  exact reverseAcc_zero_target input hsize href hrev

/-- Size 1000 and the low-64 screen make a zero mismatch the pinned vector. -/
theorem mismatch_zero_iff_target (input : ByteArray) (hsize : input.size = 1000)
    (hcond : condition input = 0) :
    TerminalXorRaw.mismatch input = 0 ↔ input = KnownInputData.targetInput := by
  constructor
  · exact mismatch_zero_target input hsize hcond
  · intro ht
    subst ht
    have href : referenceWord KnownInputData.targetInput = KnownInputData.fullWord := by
      have hread := KnownInputData.targetInput_readWord 0 (by decide : (0 : Nat) < 32)
      simpa [referenceWord, KnownInputData.expectedWord] using hread
    have heq : equalityAcc KnownInputData.targetInput 10 = 1 := by
      rw [equalityAcc_reverse, reverseAcc_target_zero]
      exact (isZero_eq_one_iff 0).2 rfl
    exact (mismatch_zero_iff _ hcond).2 ⟨href, heq⟩

#print axioms mismatch_zero_iff
#print axioms target_condition
#print axioms mismatch_zero_target
#print axioms mismatch_zero_iff_target

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath
