import Challenge.Modexp.Submission.Proofs.Memo.V9.State
import Challenge.Modexp.Submission.Proofs.Memo.V9.Paths
import Challenge.Modexp.Submission.Proofs.Memo.Step
import Challenge.Modexp.Submission.Proofs.Memo.Cover

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V9.Trace

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch State Paths

def pretestJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 2408
      stack := [UInt256.ofNat 2624, UInt256.eq (UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) (MachineState.readWord input 94)] }

def pretestJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1433 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_pretest_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock pretestPath (Main.trampolineState input 2368) =
      some (pretestJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [pretestPath, pretestJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc12, PCs.pc13, PCs.pc14,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_pretest_taken (input : ByteArray)
    (hw : MachineState.readWord input 94 = UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) :
    Challenge.EvmProof.Stepper.runLocated pretestJumpLocated (pretestJumpState input) =
      some (Main.trampolineState input 2624) := by
  have hcond : UInt256.isTrue (UInt256.eq (UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) (MachineState.readWord input 94)) := by
    rw [hw, Logic.eq_self_word]; exact Logic.isTrue_one
  have hjump : Decode.isValidJumpDest submissionBytecode 2624 = true :=
    Artifact.isValidJumpDest_index 1480 (by rfl)
  have hpc : (pretestJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1433 := by
    simp [pretestJumpState, initialState, PCs.pc13, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken pretestJumpLocated rfl (pretestJumpState input) 2624
    (UInt256.eq (UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) (MachineState.readWord input 94)) [] hpc rfl (by simp) hcond rfl (by norm_num) hjump).trans rfl

theorem run_pretest_notTaken (input : ByteArray)
    (hw : MachineState.readWord input 94 ≠ UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) :
    Challenge.EvmProof.Stepper.runLocatedBlock pretestJumpPath (pretestJumpState input) =
      some (Main.trampolineState input 2409) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat 57656776381785232221288722070333642129877090746803087510479986983448338273) (MachineState.readWord input 94) = UInt256.ofNat 0 :=
    Logic.eq_of_ne_word _ _ (fun h => hw h.symm)
  simp [pretestJumpPath, pretestJumpState, heq, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc12, PCs.pc13, PCs.pc14,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_prelude (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock preludePath (Main.trampolineState input 2409) =
      some (accState input 2414 (acc0 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [preludePath, accState, acc0, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc12, PCs.pc13, PCs.pc14,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_chunk0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock chunk0Path (accState input 2414 (acc0 input)) =
      some (accState input 2534 (acc1 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [chunk0Path, accState, acc1, chunk0, scanDiff, Data.checks, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc12, PCs.pc13, PCs.pc14,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_chunk1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock chunk1Path (accState input 2534 (acc1 input)) =
      some (accState input 2572 (acc2 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [chunk1Path, accState, acc2, chunk1, scanDiff, Data.checks, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc12, PCs.pc13, PCs.pc14,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_branch_hit (input : ByteArray) (h : guardDiff Data.checks input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPath (accState input 2572 (acc2 input)) =
      some (Main.trampolineState input 2576) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : acc2 input = UInt256.ofNat 0 := by
    rw [acc2_eq_guardDiff, h]; rfl
  simp [branchPath, accState, hz, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc12, PCs.pc13, PCs.pc14,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

def branchJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 2575
      stack := [UInt256.ofNat 1196, acc2 input] }

def branchJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1464 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

theorem run_branch_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock branchPrefixPath (accState input 2572 (acc2 input)) =
      some (branchJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [branchPrefixPath, accState, branchJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc12, PCs.pc13, PCs.pc14,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_branch_miss (input : ByteArray) (h : guardDiff Data.checks input ≠ 0) :
    Challenge.EvmProof.Stepper.runLocated branchJumpLocated (branchJumpState input) =
      some (Main.trampolineState input 1196) := by
  have hcond : UInt256.isTrue (acc2 input) :=
    Cover.isTrue_of_ne_zero _ (by rw [acc2_eq_guardDiff]; exact h)
  have hjump : Decode.isValidJumpDest submissionBytecode 1196 = true :=
    Artifact.isValidJumpDest_index 899 (by rfl)
  have hpc : (branchJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1464 := by
    simp [branchJumpState, initialState, PCs.pc13, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken branchJumpLocated rfl (branchJumpState input) 1196
    (acc2 input) [] hpc rfl (by simp) hcond rfl (by norm_num) hjump).trans rfl

theorem run_return (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock returnPath (Main.trampolineState input 2576) =
      some (returnedState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [returnPath, returnedState, answerMemory, storeWord,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc12, PCs.pc13, PCs.pc14,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

end Challenge.Modexp.Submission.Proofs.Memo.V9.Trace
