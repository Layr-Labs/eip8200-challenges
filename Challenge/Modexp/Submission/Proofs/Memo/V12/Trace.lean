import Challenge.Modexp.Submission.Proofs.Memo.V12.State
import Challenge.Modexp.Submission.Proofs.Memo.V12.Paths
import Challenge.Modexp.Submission.Proofs.Memo.Step
import Challenge.Modexp.Submission.Proofs.Memo.Cover

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V12.Trace

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch State Paths

theorem run_prelude (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock preludePath (Main.trampolineState input 3360) =
      some (accState input 3367 (acc0 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [preludePath, accState, acc0, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc18, PCs.pc19, PCs.pc20, PCs.pc21,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_chunk0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock chunk0Path (accState input 3367 (acc0 input)) =
      some (accState input 3488 (acc1 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [chunk0Path, accState, acc1, chunk0, scanDiff, Data.checks, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc18, PCs.pc19, PCs.pc20, PCs.pc21,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_chunk1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock chunk1Path (accState input 3488 (acc1 input)) =
      some (accState input 3641 (acc2 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [chunk1Path, accState, acc2, chunk1, scanDiff, Data.checks, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc18, PCs.pc19, PCs.pc20, PCs.pc21,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_chunk2 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock chunk2Path (accState input 3641 (acc2 input)) =
      some (accState input 3797 (acc3 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [chunk2Path, accState, acc3, chunk2, scanDiff, Data.checks, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc18, PCs.pc19, PCs.pc20, PCs.pc21,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_chunk3 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock chunk3Path (accState input 3797 (acc3 input)) =
      some (accState input 3953 (acc4 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [chunk3Path, accState, acc4, chunk3, scanDiff, Data.checks, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc18, PCs.pc19, PCs.pc20, PCs.pc21,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_chunk4 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock chunk4Path (accState input 3953 (acc4 input)) =
      some (accState input 4031 (acc5 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [chunk4Path, accState, acc5, chunk4, scanDiff, Data.checks, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc18, PCs.pc19, PCs.pc20, PCs.pc21,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_branch_hit (input : ByteArray) (h : guardDiff Data.checks input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPath (accState input 4031 (acc5 input)) =
      some (Main.trampolineState input 4035) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : acc5 input = UInt256.ofNat 0 := by
    rw [acc5_eq_guardDiff, h]; rfl
  simp [branchPath, accState, hz, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc18, PCs.pc19, PCs.pc20, PCs.pc21,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def branchJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4034
      stack := [UInt256.ofNat 1196, acc5 input] }

def branchJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1704 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_branch_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPrefixPath (accState input 4031 (acc5 input)) =
      some (branchJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [branchPrefixPath, accState, branchJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc18, PCs.pc19, PCs.pc20, PCs.pc21,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_branch_miss (input : ByteArray) (h : guardDiff Data.checks input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocated branchJumpLocated (branchJumpState input) =
      some (Main.trampolineState input 1196) := by
  have hcond : UInt256.isTrue (acc5 input) :=
    Cover.isTrue_of_ne_zero _ (by rw [acc5_eq_guardDiff]; exact h)
  have hjump : Decode.isValidJumpDest submissionBytecode 1196 = true :=
    Artifact.isValidJumpDest_index 899 (by rfl)
  have hpc : (branchJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1704 := by
    simp [branchJumpState, initialState, PCs.pc20, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken branchJumpLocated rfl (branchJumpState input) 1196
    (acc5 input) [] hpc rfl (by simp) hcond rfl (by norm_num) hjump).trans rfl

theorem run_return (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock returnPath (Main.trampolineState input 4035) =
      some (returnedState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [returnPath, returnedState, answerMemory, storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc18, PCs.pc19, PCs.pc20, PCs.pc21,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

end Challenge.Modexp.Submission.Proofs.Memo.V12.Trace
