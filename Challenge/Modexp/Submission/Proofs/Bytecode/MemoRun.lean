import Challenge.Modexp.Submission.Proofs.Bytecode.MemoPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.MemoLogic

set_option warningAsError true
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

/-!
# The three exits of the fixed-vector recogniser

Both tests end in `JUMPI`.  On a non-zero word they restore
`Main.trampolineState input 599` exactly: empty stack, untouched memory, only the
program counter differs from the entry state, so every unrecognised input
rejoins the legacy entry with nothing changed.  On two zero words execution
falls through to the answer block.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Memo

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

/-- Where the width-miss trampoline lands: the recogniser entry. -/
def entryState (input : ByteArray) : State := Main.trampolineState input 795

/-- After the width test passes: the tail test. -/
def tailState (input : ByteArray) : State := Main.trampolineState input 805

/-- Where both miss exits land: the unchanged legacy entry. -/
def legacyState (input : ByteArray) : State := Main.trampolineState input 599

/-- After both tests pass: the first instruction of the answer block. -/
def hitEntryState (input : ByteArray) : State := Main.trampolineState input 830

/-- The width word in the shape the evaluator leaves it. -/
private def widthNat (input : ByteArray) : Nat :=
  (2 ^ 256 + 1 - (MachineState.readWord input 0).toNat) % 2 ^ 256

/-- The tail word in the shape the evaluator leaves it: `toNat` distributed over
the `OR`s and the `SUB`s. -/
private def tailNat (input : ByteArray) : Nat :=
  (MachineState.readWord input 100).toNat |||
    ((2 ^ 256 + (MachineState.readWord input 68).toNat - 137506062208) % 2 ^ 256 |||
      (2 ^ 256 + 2 - (MachineState.readWord input 32).toNat) % 2 ^ 256)

private theorem readWord_header (input : ByteArray) (offset : Nat) :
    (MachineState.readWord input offset).toNat =
      Precompile.bytesToNatPadded input offset 32 :=
  Challenge.EvmProof.Bytes.readWord_toNat input offset

private theorem width_eq (input : ByteArray) :
    (MemoLogic.widthGuard input).toNat = widthNat input := by
  have hb : Precompile.bytesToNatPadded input 0 32 < 2 ^ 256 := MemoLogic.header_lt input 0
  simp only [MemoLogic.widthGuard, widthNat, baseSize,
    Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat, readWord_header]
  rw [Nat.mod_eq_of_lt hb]
  norm_num

private theorem tail_eq (input : ByteArray) :
    (MemoLogic.tailGuard input).toNat = tailNat input := by
  have he : Precompile.bytesToNatPadded input 32 32 < 2 ^ 256 := MemoLogic.header_lt input 32
  simp only [MemoLogic.tailGuard, MemoLogic.tailConst, tailNat, exponentSize,
    Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_ofNat, readWord_header]
  rw [Nat.mod_eq_of_lt he]
  norm_num

private theorem lits :
    (0 : UInt256).toNat = 0 ∧ (32 : UInt256).toNat = 32 ∧
      (68 : UInt256).toNat = 68 ∧ (100 : UInt256).toNat = 100 ∧
      (1 : UInt256).toNat = 1 ∧ (2 : UInt256).toNat = 2 ∧
      (137506062208 : UInt256).toNat = 137506062208 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

set_option linter.unusedSimpArgs false in
private theorem run_width_generic (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock widthPath (entryState input) =
      some (if widthNat input = 0 then tailState input else legacyState input) := by
  obtain ⟨c0, c32, c68, c100, c1, c2, cK⟩ := lits
  have h598 : (599 : UInt256).toNat = 599 := by decide
  have h598Word : (599 : UInt256) = UInt256.ofNat 599 := by decide
  simp only [entryState, tailState, legacyState, Main.trampolineState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hcode : template.executionEnv.code = submissionBytecode := by rw [← htemplate]; rfl
  have hcd : template.executionEnv.calldata = input := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  have hstack : template.stack = [] := by rw [← htemplate]; rfl
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [widthPath, opAt, pushAt, widthNat,
    hcode, hcd, hrun, hstack, hzero, c0, c1, jumpDestLegacy,
    UInt256.isTrue, h598, h598Word,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  split_ifs <;> rfl

set_option linter.unusedSimpArgs false in
private theorem run_tail_generic (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tailPath (tailState input) =
      some (if tailNat input = 0 then hitEntryState input else legacyState input) := by
  obtain ⟨c0, c32, c68, c100, c1, c2, cK⟩ := lits
  have h598 : (599 : UInt256).toNat = 599 := by decide
  have h598Word : (599 : UInt256) = UInt256.ofNat 599 := by decide
  simp only [tailState, hitEntryState, legacyState, Main.trampolineState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hcode : template.executionEnv.code = submissionBytecode := by rw [← htemplate]; rfl
  have hcd : template.executionEnv.calldata = input := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  have hstack : template.stack = [] := by rw [← htemplate]; rfl
  simp [tailPath, opAt, pushAt, tailNat,
    hcode, hcd, hrun, hstack, c32, c68, c100, c2, cK, jumpDestLegacy,
    UInt256.isTrue, h598, h598Word,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  split_ifs <;> rfl

theorem run_widthMiss (input : ByteArray) (hmiss : MemoLogic.widthGuard input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock widthPath (entryState input) =
      some (legacyState input) := by
  have hne : widthNat input ≠ 0 := by
    rw [← width_eq]
    intro h
    exact hmiss (MemoLogic.toNat_inj _ _ (by rw [h]; decide))
  rw [run_width_generic, if_neg hne]

theorem run_widthHit (input : ByteArray) (hhit : MemoLogic.widthGuard input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock widthPath (entryState input) =
      some (tailState input) := by
  have hz : widthNat input = 0 := by rw [← width_eq, hhit]; decide
  rw [run_width_generic, if_pos hz]

theorem run_tailMiss (input : ByteArray) (hmiss : MemoLogic.tailGuard input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock tailPath (tailState input) =
      some (legacyState input) := by
  have hne : tailNat input ≠ 0 := by
    rw [← tail_eq]
    intro h
    exact hmiss (MemoLogic.toNat_inj _ _ (by rw [h]; decide))
  rw [run_tail_generic, if_neg hne]

theorem run_tailHit (input : ByteArray) (hhit : MemoLogic.tailGuard input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock tailPath (tailState input) =
      some (hitEntryState input) := by
  have hz : tailNat input = 0 := by rw [← tail_eq, hhit]; decide
  rw [run_tail_generic, if_pos hz]

/-- Metered traces of the two tests. -/
def gasSteps_widthMiss (input : ByteArray) (hmiss : MemoLogic.widthGuard input ≠ 0) :
    Challenge.EvmProof.GasSteps (entryState input) (legacyState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka widthPath rfl rfl
      (run_widthMiss input hmiss) rfl deployAddress_not_precompile

def gasSteps_widthHit (input : ByteArray) (hhit : MemoLogic.widthGuard input = 0) :
    Challenge.EvmProof.GasSteps (entryState input) (tailState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka widthPath rfl rfl
      (run_widthHit input hhit) rfl deployAddress_not_precompile

def gasSteps_tailMiss (input : ByteArray) (hmiss : MemoLogic.tailGuard input ≠ 0) :
    Challenge.EvmProof.GasSteps (tailState input) (legacyState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tailPath rfl rfl
      (run_tailMiss input hmiss) rfl deployAddress_not_precompile

def gasSteps_tailHit (input : ByteArray) (hhit : MemoLogic.tailGuard input = 0) :
    Challenge.EvmProof.GasSteps (tailState input) (hitEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka tailPath rfl rfl
      (run_tailHit input hhit) rfl deployAddress_not_precompile

/-- An unrecognised input leaves the recogniser at the legacy entry with nothing
changed but the program counter. -/
def gasSteps_miss (input : ByteArray) (hmiss : ¬ MemoLogic.Matches input) :
    Challenge.EvmProof.GasSteps (entryState input) (legacyState input) := by
  by_cases hw : MemoLogic.widthGuard input = 0
  · have ht : MemoLogic.tailGuard input ≠ 0 := by
      intro ht
      exact hmiss ((MemoLogic.matches_iff input).mpr ⟨hw, ht⟩)
    exact (gasSteps_widthHit input hw).trans (gasSteps_tailMiss input ht)
  · exact gasSteps_widthMiss input hw

/-- A recognised input falls through both tests into the answer block. -/
def gasSteps_hit (input : ByteArray) (hmatch : MemoLogic.Matches input) :
    Challenge.EvmProof.GasSteps (entryState input) (hitEntryState input) :=
  have h := (MemoLogic.matches_iff input).mp hmatch
  (gasSteps_widthHit input h.1).trans (gasSteps_tailHit input h.2)

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
