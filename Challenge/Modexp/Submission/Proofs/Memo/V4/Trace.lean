import Challenge.Modexp.Submission.Proofs.Memo.V4.State
import Challenge.Modexp.Submission.Proofs.Memo.V4.Paths
import Challenge.Modexp.Submission.Proofs.Memo.Step

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V4.Trace

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch State Paths

theorem run_prelude (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock preludePath (Main.trampolineState input 1633) =
      some (accState input 1639 (acc0 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [preludePath, accState, acc0, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc4, PCs.pc5,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_chunk0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock chunk0Path (accState input 1639 (acc0 input)) =
      some (accState input 1691 (acc1 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [chunk0Path, accState, acc1, chunk0, scanDiff, Data.checks, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc4, PCs.pc5,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def branchJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1695
      stack := [UInt256.ofNat 1700, UInt256.ofNat 1] }

def branch_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1148 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_branch_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated branch_jumpLocated (branchJumpState input) =
      some (Main.trampolineState input 1700) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1700 = true :=
    Artifact.isValidJumpDest_index 1151 (by rfl)
  have hpc : (branchJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1148 := by
    simp [branchJumpState, initialState, PCs.pc4, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken branch_jumpLocated rfl (branchJumpState input) 1700 (UInt256.ofNat 1) [] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_branch_match_prefix (input : ByteArray) (h : guardDiff Data.checks input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPrefixPath (accState input 1691 (acc1 input)) =
      some (branchJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : UInt256.isZero (acc1 input) = UInt256.ofNat 1 := by
    rw [acc1_eq_guardDiff]; exact Logic.isZero_of_eq _ h
  simp [branchPrefixPath, branchJumpState, accState, hz, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc4, PCs.pc5,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_branch_mismatch (input : ByteArray) (h : guardDiff Data.checks input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPath (accState input 1691 (acc1 input)) =
      some (Main.trampolineState input 1696) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : UInt256.isZero (acc1 input) = UInt256.ofNat 0 := by
    rw [acc1_eq_guardDiff]; exact Logic.isZero_of_ne _ h
  simp [branchPath, accState, hz, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc4, PCs.pc5,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def fallbackJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1699
      stack := [UInt256.ofNat 1196] }

def fallback_jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1150 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

theorem run_fallback_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated fallback_jumpLocated (fallbackJumpState input) =
      some (Main.trampolineState input 1196) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1196 = true :=
    Artifact.isValidJumpDest_index 899 (by rfl)
  have hpc : (fallbackJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1150 := by
    simp [fallbackJumpState, initialState, PCs.pc4, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jump fallback_jumpLocated rfl (fallbackJumpState input) 1196 [] hpc rfl (by simp) rfl (by norm_num) hjump).trans rfl

theorem run_fallback_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock fallbackPrefixPath (Main.trampolineState input 1696) =
      some (fallbackJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [fallbackPrefixPath, fallbackJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc4, PCs.pc5,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_return (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock returnPath (Main.trampolineState input 1700) =
      some (returnedState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [returnPath, returnedState, answerMemory, storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc4, PCs.pc5,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

end Challenge.Modexp.Submission.Proofs.Memo.V4.Trace
