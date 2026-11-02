import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.MemoRun
import Challenge.Modexp.Submission.Proofs.Bytecode.MemoCert
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FermatProgram

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 400000
set_option maxHeartbeats 4000000

/-!
# The answer block of the fixed-vector memo

The recognised tuple pins every byte the specification reads, so its result is the
constant `MemoCert.answer = 3^65535 mod 2^255`.  The hit exit at pc 733 jumps to a
landing pad at pc 61 that pushes the precomputed word, stores it at 0 and returns
`MSIZE` (one word) bytes from 0 on the untouched memory.  No `EXP` is executed.
-/

namespace CycleSubmission.Global.Memo
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM
open CycleSubmission.Global.Dispatch
open YulEvmCompiler Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

/-- The answer block's landing pad at pc 61. -/
theorem jumpDestAnswer :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 61 = true :=
  CycleSubmission.Global.Binding.jumpDest 40 (by rfl)

/-- After the jump: the landing pad at pc 61 with an empty stack. -/
def answerEntryState (input : ByteArray) : State := Main.trampolineState input 61

set_option linter.unusedSimpArgs false in
theorem run_hitPre (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock hitPrePath (hitEntryState input) =
      some (answerEntryState input) := by
  simp only [hitEntryState, answerEntryState, Main.trampolineState]
  generalize htemplate : initialState CycleSubmission.Artifact.bytecode input 0 = template
  have hcode : template.executionEnv.code = CycleSubmission.Artifact.bytecode := by rw [← htemplate]; rfl
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  have hstack : template.stack = [] := by rw [← htemplate]; rfl
  have hj : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode
      (61 : UInt256).toNat = true := jumpDestAnswer
  have hpc60 : (61 : UInt256) = UInt256.ofNat 61 := rfl
  simp [hitPrePath, opAt, pushAt, hcode, hrun, hstack, hj, hpc60,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod]
  all_goals first | decide | (cases template; simp_all)

def gasSteps_hitPre (input : ByteArray) :
    Challenge.EvmProof.GasSteps (hitEntryState input) (answerEntryState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    CycleSubmission.Artifact.artifact .Osaka hitPrePath rfl rfl
      (run_hitPre input) rfl deployAddress_not_precompile

/-- The answer word the block returns: the `PUSH32` literal, `MemoCert.answer`. -/
def answerWord : UInt256 :=
  26689440342447178617115869845918039756797228267049433585260346420242739014315

/-- The answer block at pc 61: `JUMPDEST PUSH32 answer PUSH0 MSTORE MSIZE PUSH0 RETURN`. -/
def padProgram : List Instr :=
  [.op .JUMPDEST, .push 32 answerWord] ++ FermatProgram.exitProgram

def padBlock :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 61 padProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 40 7 61 padProgram
    (by exact Nat.le_trans (by decide : 40+7 ≤ 8670) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm))
    (by rfl) (by rfl) (by decide)

/-- The halted state the block returns from. -/
def hitFinalState (input : ByteArray) : State :=
  WindowTwentyOneReturn.returned (answerEntryState input) (UInt256.ofNat 99) answerWord 0 []

theorem run_pad (input : ByteArray) :
    WindowTwentyOneMsize.runInstructionsX padProgram (answerEntryState input) =
      some (hitFinalState input) := by
  have hpre : WindowTwentyOneMsize.runInstructionsX [.op .JUMPDEST, .push 32 answerWord]
      (answerEntryState input) =
      some (WindowTwentyOneReturn.framed (answerEntryState input) (UInt256.ofNat 95) [answerWord]) := by
    rw [WindowTwentyOneMsize.runInstructionsX_eq _ (by decide)]
    have hs : (answerEntryState input).stack = [] := rfl
    simp [WindowNibbleKernel.runInstructions, WindowTwentyOneReturn.framed, answerEntryState,
      Main.trampolineState, Challenge.EvmProof.Stepper.runInstr, initialState,
      Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod]
  have hexit := FermatProgram.run_exit (answerEntryState input) (UInt256.ofNat 95) answerWord rfl []
    (by simp)
  have hpc : advancePC 4 (UInt256.ofNat 95) = UInt256.ofNat 99 := by decide
  rw [hpc] at hexit
  exact WindowTwentyOneMsize.runInstructionsX_append_some _ _ _ _ _ hpre hexit

def gasSteps_hitPost (input : ByteArray) :
    Challenge.EvmProof.GasSteps (answerEntryState input) (hitFinalState input) :=
  WindowTwentyOneMsize.Block.stepsX padBlock
    { sizeBound := by
        change CycleSubmission.Artifact.bytecode.size < 2 ^ 256
        rw [CycleSubmission.Artifact.bytecodeSize]
        norm_num
      code := rfl
      forkEq := rfl
      running := rfl
      noPrecompile := deployAddress_not_precompile }
    rfl (run_pad input)

theorem answerWord_toNat : answerWord.toNat = MemoCert.answer := rfl

theorem hitFinalState_isDone (input : ByteArray) :
    (hitFinalState input).isDone = true := rfl

theorem hitFinalState_result (input : ByteArray) (hvalid : ValidInput input)
    (hmatch : MemoLogic.Matches input) :
    (hitFinalState input).toResult = .returned (Challenge.Modexp.spec input) := by
  rw [MemoCert.spec_eq input hvalid hmatch, hitFinalState, WindowTwentyOneReturn.returned_result,
    answerWord_toNat]

/-- The answer block returns the specified result for every recognised input. -/
theorem hitHandled (input : ByteArray) (hvalid : ValidInput input)
    (hmatch : MemoLogic.Matches input) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps (entryState input) final) ∧
        final.isDone = true ∧ final.toResult = .returned (Challenge.Modexp.spec input) :=
  ⟨hitFinalState input,
    ⟨(gasSteps_hit input hmatch).trans
      ((gasSteps_hitPre input).trans (gasSteps_hitPost input))⟩,
    hitFinalState_isDone input, hitFinalState_result input hvalid hmatch⟩

end CycleSubmission.Global.Memo
