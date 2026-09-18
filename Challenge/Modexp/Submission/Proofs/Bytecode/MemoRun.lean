import Challenge.Modexp.Submission.Proofs.Bytecode.MemoPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.MemoLogic

set_option warningAsError true
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

/-!
# The two exits of the appended fixed-vector block

The recognition prefix ends in `JUMPI`.  On a non-zero accumulator it restores
`Dispatch.wordDispatchState` exactly — same stack, only the program counter
differs from the entry state — so every unrecognised input rejoins the inherited
dispatcher with nothing changed.  On a zero accumulator it falls through to the
answer block.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Memo

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

/-- State at the recogniser's own hit exit: the jump to the answer block. -/
def hitJumpState (input : ByteArray) : State :=
  { guardEntryState input with pc := UInt256.ofNat 5290 }

/-- State at the first instruction of the appended answer block. -/
def hitEntryState (input : ByteArray) : State :=
  { guardEntryState input with pc := UInt256.ofNat 5433 }

/-- The accumulator in the shape the evaluator leaves it: `toNat` distributed
over the `OR`s and the `SUB`s, with the header words reduced. -/
private def accNat (input : ByteArray) : Nat :=
  (2 ^ 256 + 2 - exponentSize input % 2 ^ 256) % 2 ^ 256 |||
    ((MachineState.readWord input 100).toNat |||
      ((2 ^ 256 + (MachineState.readWord input 68).toNat - 137506062208) % 2 ^ 256 |||
        (2 ^ 256 + 1 - baseSize input % 2 ^ 256) % 2 ^ 256))

private theorem acc_eq (input : ByteArray) :
    (MemoLogic.guardDiff input).toNat = accNat input := by
  simp only [MemoLogic.guardDiff, MemoLogic.tailConst, accNat,
    Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num

private theorem lits :
    (68 : UInt256).toNat = 68 ∧ (100 : UInt256).toNat = 100 ∧
      (1 : UInt256).toNat = 1 ∧ (2 : UInt256).toNat = 2 ∧
      (137506062208 : UInt256).toNat = 137506062208 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

set_option linter.unusedSimpArgs false in
private theorem run_guard_generic (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock guardPath (guardEntryState input) =
      some (if accNat input = 0 then hitJumpState input else wordDispatchState input) := by
  obtain ⟨c68, c100, c1, c2, cK⟩ := lits
  have h570 : (570 : UInt256).toNat = 570 := by decide
  have h570Word : (570 : UInt256) = UInt256.ofNat 570 := by decide
  simp only [hitJumpState, guardEntryState, wordDispatchState, Main.headerState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hcode : template.executionEnv.code = submissionBytecode := by rw [← htemplate]; rfl
  have hcd : template.executionEnv.calldata = input := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  simp [guardPath, opAt, pushAt, accNat,
    hcode, hcd, hrun, c68, c100, c1, c2, cK,
    UInt256.isTrue, h570, h570Word,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  -- the evaluator wraps its result in `match _ with | none => none | some n => some n`
  split_ifs <;> rfl

theorem run_guardMiss (input : ByteArray) (hmiss : MemoLogic.guardDiff input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock guardPath
      (guardEntryState input) = some (wordDispatchState input) := by
  have hne : accNat input ≠ 0 := by
    rw [← acc_eq]
    intro h
    exact hmiss (MemoLogic.toNat_inj _ _ (by rw [h]; decide))
  rw [run_guard_generic, if_neg hne]

theorem run_guardHit (input : ByteArray) (hhit : MemoLogic.guardDiff input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock guardPath
      (guardEntryState input) = some (hitJumpState input) := by
  have hz : accNat input = 0 := by rw [← acc_eq, hhit]; decide
  rw [run_guard_generic, if_pos hz]

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
/-- The recogniser's hit exit: a JUMPI whose condition is the declared modulus
size, which is non-zero on every input that reaches the recogniser. -/
theorem run_hitJump (input : ByteArray) (hvalid : ValidInput input)
    (hpositive : 0 < modulusSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock hitJumpPath (hitJumpState input) =
      some (hitEntryState input) := by
  rcases hvalid with ⟨_, _, _, hm⟩
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hmodNat : modulusSize input % 2 ^ 256 ≠ 0 := by
    rw [Nat.mod_eq_of_lt hm']; omega
  norm_num at hmodNat
  have h5428 : (5433 : UInt256).toNat = 5433 := by decide
  have h5428Word : (5433 : UInt256) = UInt256.ofNat 5433 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat (modulusSize input)) := hmodNat
  simp only [hitJumpState, hitEntryState, guardEntryState, wordDispatchState, Main.headerState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hcode : template.executionEnv.code = submissionBytecode := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  simp [hitJumpPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcode, hrun, hmodNat, h5428, h5428Word, htrue, UInt256.isTrue,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
