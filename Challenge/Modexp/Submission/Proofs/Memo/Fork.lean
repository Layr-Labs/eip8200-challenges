import Challenge.Modexp.Submission.Proofs.Memo.V2
import Challenge.Modexp.Submission.Proofs.Memo.V2.Data
import Challenge.Modexp.Submission.Proofs.Memo.V3
import Challenge.Modexp.Submission.Proofs.Memo.V3.Data
import Challenge.Modexp.Submission.Proofs.Memo.V9
import Challenge.Modexp.Submission.Proofs.Memo.V9.Data
import Challenge.Modexp.Submission.Proofs.Memo.V10
import Challenge.Modexp.Submission.Proofs.Memo.V10.Data
import Challenge.Modexp.Submission.Proofs.Memo.Step

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.Fork

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch

def v9Word : Nat :=
  5964364953636342908918930162962566239787286640968493902593843747347131818633

def v10Word : Nat :=
  73247641362558725300106169323372519318985509881989093824173738694050148637181

theorem hit2_word32 (input : ByteArray) (h : guardDiff V2.Data.checks input = 0) :
    MachineState.readWord input 32 = 0 := by
  have hm : WordsMatch V2.Data.checks input := (guardDiff_eq_zero_iff _ _).1 h
  exact hm (32, 0) (by decide)

theorem hit3_word32 (input : ByteArray) (h : guardDiff V3.Data.checks input = 0) :
    MachineState.readWord input 32 = 1 := by
  have hm : WordsMatch V3.Data.checks input := (guardDiff_eq_zero_iff _ _).1 h
  exact hm (32, 1) (by decide)

theorem hit9_word96 (input : ByteArray) (h : guardDiff V9.Data.checks input = 0) :
    MachineState.readWord input 96 = UInt256.ofNat v9Word := by
  have hm : WordsMatch V9.Data.checks input := (guardDiff_eq_zero_iff _ _).1 h
  exact hm (96, UInt256.ofNat v9Word) (by decide)

theorem hit10_word96 (input : ByteArray) (h : guardDiff V10.Data.checks input = 0) :
    MachineState.readWord input 96 = UInt256.ofNat v10Word := by
  have hm : WordsMatch V10.Data.checks input := (guardDiff_eq_zero_iff _ _).1 h
  exact hm (96, UInt256.ofNat v10Word) (by decide)

def fork98PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1683 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1684 1 32,
   Main.opAt 1685 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1686 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1687 2 1473
  ]

def fork98JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4217
      stack := [UInt256.ofNat 1473, UInt256.ofNat 1] }

def fork98JumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1688 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def fork98SkipPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1683 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1684 1 32,
   Main.opAt 1685 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.opAt 1686 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.ISZERO)),
   Main.pushAt 1687 2 1473,
   Main.opAt 1688 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def fork98FallPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1689 2 1553
  ]

def fork98FallJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4221
      stack := [UInt256.ofNat 1553] }

def fork98FallJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1690 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

theorem run_fork98_prefix_zero (input : ByteArray)
    (hw : MachineState.readWord input 32 = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock fork98PrefixPath (Main.trampolineState input 4209) =
      some (fork98JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : UInt256.isZero (MachineState.readWord input 32) = UInt256.ofNat 1 :=
    Logic.isZero_of_eq _ hw
  simp [fork98PrefixPath, fork98JumpState, hz, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc20,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_fork98_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated fork98JumpLocated (fork98JumpState input) =
      some (Main.trampolineState input 1473) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1473 = true :=
    Artifact.isValidJumpDest_index 1051 (by rfl)
  have hpc : (fork98JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1688 := by
    simp [fork98JumpState, initialState, PCs.pc20, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken fork98JumpLocated rfl (fork98JumpState input) 1473 (UInt256.ofNat 1) [] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_fork98_skip (input : ByteArray)
    (hw : MachineState.readWord input 32 ≠ 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock fork98SkipPath (Main.trampolineState input 4209) =
      some (Main.trampolineState input 4218) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hz : UInt256.isZero (MachineState.readWord input 32) = UInt256.ofNat 0 :=
    Logic.isZero_of_ne _ hw
  simp [fork98SkipPath, hz, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc20,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_fork98_fall_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock fork98FallPrefixPath (Main.trampolineState input 4218) =
      some (fork98FallJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [fork98FallPrefixPath, fork98FallJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc20,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_fork98_fall_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated fork98FallJumpLocated (fork98FallJumpState input) =
      some (Main.trampolineState input 1553) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1553 = true :=
    Artifact.isValidJumpDest_index 1087 (by rfl)
  have hpc : (fork98FallJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1690 := by
    simp [fork98FallJumpState, initialState, PCs.pc20, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jump fork98FallJumpLocated rfl (fork98FallJumpState input) 1553 [] hpc rfl (by simp) rfl (by norm_num) hjump).trans rfl

def fork192PrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1694 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1695 1 96,
   Main.opAt 1696 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 1697 32 v9Word,
   Main.opAt 1698 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1699 2 2305
  ]

def fork192JumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4266
      stack := [UInt256.ofNat 2305, UInt256.ofNat 1] }

def fork192JumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1700 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def fork192SkipPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1694 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.pushAt 1695 1 96,
   Main.opAt 1696 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATALOAD)),
   Main.pushAt 1697 32 v9Word,
   Main.opAt 1698 (EvmSemantics.Operation.CompBit (EvmSemantics.Operation.CompareBitwiseOps.EQ)),
   Main.pushAt 1699 2 2305,
   Main.opAt 1700 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def fork192FallPrefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1701 2 2497
  ]

def fork192FallJumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4270
      stack := [UInt256.ofNat 2497] }

def fork192FallJumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1702 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMP))

theorem run_fork192_prefix_hit (input : ByteArray)
    (hw : MachineState.readWord input 96 = UInt256.ofNat v9Word) :
    Challenge.EvmProof.Stepper.runLocatedBlock fork192PrefixPath (Main.trampolineState input 4225) =
      some (fork192JumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat v9Word) (MachineState.readWord input 96) = UInt256.ofNat 1 := by
    rw [hw]; exact Logic.eq_ofNat_of_eq rfl
  simp [fork192PrefixPath, fork192JumpState, heq, v9Word, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc20,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_fork192_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated fork192JumpLocated (fork192JumpState input) =
      some (Main.trampolineState input 2305) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 2305 = true :=
    Artifact.isValidJumpDest_index 1352 (by rfl)
  have hpc : (fork192JumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1700 := by
    simp [fork192JumpState, initialState, PCs.pc20, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken fork192JumpLocated rfl (fork192JumpState input) 2305 (UInt256.ofNat 1) [] hpc rfl (by simp) Logic.isTrue_one rfl (by norm_num) hjump).trans rfl

theorem run_fork192_skip (input : ByteArray)
    (hw : MachineState.readWord input 96 ≠ UInt256.ofNat v9Word) :
    Challenge.EvmProof.Stepper.runLocatedBlock fork192SkipPath (Main.trampolineState input 4225) =
      some (Main.trampolineState input 4267) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have heq : UInt256.eq (UInt256.ofNat v9Word) (MachineState.readWord input 96) = UInt256.ofNat 0 := by
    revert hw
    simp [UInt256.eq, v9Word]
    intro hw
    exact if_neg (Ne.symm hw)
  simp [fork192SkipPath, heq, v9Word, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc20,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_fork192_fall_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock fork192FallPrefixPath (Main.trampolineState input 4267) =
      some (fork192FallJumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [fork192FallPrefixPath, fork192FallJumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc20,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_fork192_fall_jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocated fork192FallJumpLocated (fork192FallJumpState input) =
      some (Main.trampolineState input 2497) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 2497 = true :=
    Artifact.isValidJumpDest_index 1403 (by rfl)
  have hpc : (fork192FallJumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1702 := by
    simp [fork192FallJumpState, initialState, PCs.pc20, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jump fork192FallJumpLocated rfl (fork192FallJumpState input) 2497 [] hpc rfl (by simp) rfl (by norm_num) hjump).trans rfl

end Challenge.Modexp.Submission.Proofs.Memo.Fork
