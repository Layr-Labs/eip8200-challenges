import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoadedCalls
import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoadedHoistHelper

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundSitesRight

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

abbrev Artifact := QuadSites.Artifact

abbrev NormalIndex := Fin 9

def normalFin (k : NormalIndex) : Fin 20 :=
  ⟨(k.val + 3) + (k.val + 3) / 3, by omega⟩

private theorem normal_slice (k : NormalIndex) :
    (Artifact.instructions.drop (rightWrapperIndex (normalFin k).val)).take
        (LoadedCalls.ShiftedCall.quadCallPushes (rightReturnPC (normalFin k).val)
          (rightAddress0 (normalFin k)) (rightAddress1 (normalFin k))
          (rightAddress2 (normalFin k)) (rightAddress3 (normalFin k))
          (rightHelperPC (normalFin k).val) (rightRotation0 (normalFin k))
          (rightRotation1 (normalFin k)) (rightRotation2 (normalFin k))
          (rightRotation3 (normalFin k))).length =
      LoadedCalls.ShiftedCall.quadCallPushes (rightReturnPC (normalFin k).val)
        (rightAddress0 (normalFin k)) (rightAddress1 (normalFin k))
        (rightAddress2 (normalFin k)) (rightAddress3 (normalFin k))
        (rightHelperPC (normalFin k).val) (rightRotation0 (normalFin k))
        (rightRotation1 (normalFin k)) (rightRotation2 (normalFin k))
        (rightRotation3 (normalFin k)) := by
  fin_cases k <;>
    simp only [normalFin, rightReturnPC, QuadLayout.rightReturnPC,
      ArtifactByteLength.instructionPC_eq_byteLength] <;> rfl

private theorem normal_fits (k : NormalIndex) :
    rightWrapperIndex (normalFin k).val +
        (LoadedCalls.ShiftedCall.quadCallPushes (rightReturnPC (normalFin k).val)
          (rightAddress0 (normalFin k)) (rightAddress1 (normalFin k))
          (rightAddress2 (normalFin k)) (rightAddress3 (normalFin k))
          (rightHelperPC (normalFin k).val) (rightRotation0 (normalFin k))
          (rightRotation1 (normalFin k)) (rightRotation2 (normalFin k))
          (rightRotation3 (normalFin k))).length ≤
      Artifact.instructions.length := by
  fin_cases k <;> decide

private theorem normal_wellFormed (k : NormalIndex) :
    ∀ instruction ∈ LoadedCalls.ShiftedCall.quadCallPushes
        (rightReturnPC (normalFin k).val)
        (rightAddress0 (normalFin k)) (rightAddress1 (normalFin k))
        (rightAddress2 (normalFin k)) (rightAddress3 (normalFin k))
        (rightHelperPC (normalFin k).val) (rightRotation0 (normalFin k))
        (rightRotation1 (normalFin k)) (rightRotation2 (normalFin k))
        (rightRotation3 (normalFin k)),
      Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  exact StackRoundData.templateWellFormed_mem (by
    fin_cases k <;> decide) instruction hmem

def normalPushes (k : NormalIndex) :
    GenericRoundSite Artifact .Osaka
      (LoadedCalls.ShiftedCall.quadCallPushes (rightReturnPC (normalFin k).val)
        (rightAddress0 (normalFin k)) (rightAddress1 (normalFin k))
        (rightAddress2 (normalFin k)) (rightAddress3 (normalFin k))
        (rightHelperPC (normalFin k).val) (rightRotation0 (normalFin k))
        (rightRotation1 (normalFin k)) (rightRotation2 (normalFin k))
        (rightRotation3 (normalFin k))) :=
  StackSiteBuilder.ofSlice _ (rightWrapperIndex (normalFin k).val) (normal_slice k)
    (normal_fits k) QuadLayout.code_bound (normal_wellFormed k)
    (by simp [LoadedCalls.ShiftedCall.quadCallPushes])

def normalJump (k : NormalIndex) : LocatedSite Artifact .Osaka where
  located :=
    { index := rightWrapperIndex (normalFin k).val + 15
      instruction := .op .JUMP
      atIndex := by
        fin_cases k <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := rightJumpPC (normalFin k).val
  pc_eq := QuadLayout.pc_toNat_instructionPC _

private theorem normalPushes_end (k : NormalIndex) :
    (normalJump k).pc = (normalPushes k).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (normalPushes k).sites (normalPushes k).startPC (normalPushes k).endPC
    (normalPushes k).head_eq (normalPushes k).end_eq
    (normalPushes k).contiguous
  rw [(normalPushes k).instruction_eq] at hend
  have hstart : (normalPushes k).startPC = rightPC (normalFin k).val := by rfl
  rw [hstart] at hend
  calc
    (normalJump k).pc = rightJumpPC (normalFin k).val := by rfl
    _ = StackRoundTrace.pcAfter (rightPC (normalFin k).val)
        (LoadedCalls.ShiftedCall.quadCallPushes (rightReturnPC (normalFin k).val)
          (rightAddress0 (normalFin k)) (rightAddress1 (normalFin k))
          (rightAddress2 (normalFin k)) (rightAddress3 (normalFin k))
          (rightHelperPC (normalFin k).val) (rightRotation0 (normalFin k))
          (rightRotation1 (normalFin k)) (rightRotation2 (normalFin k))
          (rightRotation3 (normalFin k))) := by
      fin_cases k <;>
        simp only [normalFin, rightPC, rightJumpPC, rightReturnPC,
          QuadLayout.rightPC, QuadLayout.rightJumpPC,
          QuadLayout.rightReturnPC,
          ArtifactByteLength.instructionPC_eq_byteLength] <;> rfl
    _ = (normalPushes k).endPC := hend.symm

def normalReturn (k : NormalIndex) : LocatedSite Artifact .Osaka where
  located :=
    { index := QuadLayout.rightReturnIndex (normalFin k).val
      instruction := .op .JUMPDEST
      atIndex := by
        fin_cases k <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := rightReturnPC (normalFin k).val
  pc_eq := QuadLayout.pc_toNat_instructionPC _

def normalCall (k : NormalIndex) :
    LoadedCalls.ShiftedCall.CallSite Artifact .Osaka
      (rightReturnPC (normalFin k).val)
      (rightAddress0 (normalFin k)) (rightAddress1 (normalFin k))
      (rightAddress2 (normalFin k)) (rightAddress3 (normalFin k))
      (rightHelperPC (normalFin k).val)
      (rightRotation0 (normalFin k)) (rightRotation1 (normalFin k))
      (rightRotation2 (normalFin k)) (rightRotation3 (normalFin k)) where
  pushes := normalPushes k
  jump := normalJump k
  jump_instr := rfl
  jump_pc := normalPushes_end k

private theorem helper_slice (group : Fin 3) :
    (Artifact.instructions.drop (rightHelperStartIndex (group.val + 1))).take
        (rightHelperTemplate ⟨(group.val + 1), by omega⟩).length = rightHelperTemplate ⟨(group.val + 1), by omega⟩ := by
  fin_cases group <;> rfl

def helperSite (group : Fin 3) :
    GenericRoundSite Artifact .Osaka (rightHelperTemplate ⟨(group.val + 1), by omega⟩) :=
  StackSiteBuilder.ofSlice _ (rightHelperStartIndex (group.val + 1))
    (helper_slice group)
    (by fin_cases group <;> decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by fin_cases group <;> decide))
    (by fin_cases group <;> decide)

def helperJump (group : Fin 3) : LocatedSite Artifact .Osaka where
  located :=
    { index := rightHelperJumpIndex (group.val + 1)
      instruction := .op .JUMP
      atIndex := by fin_cases group <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.instructionPC (rightHelperJumpIndex (group.val + 1)))
  pc_eq := QuadLayout.pc_toNat_instructionPC _

private theorem helper_start (group : Fin 3) :
    (helperSite group).startPC = rightHelperPCOfGroup (group.val + 1) := by
  fin_cases group <;> rfl

private theorem helper_end (group : Fin 3) :
    (helperJump group).pc = (helperSite group).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (helperSite group).sites (helperSite group).startPC (helperSite group).endPC
    (helperSite group).head_eq (helperSite group).end_eq
    (helperSite group).contiguous
  rw [(helperSite group).instruction_eq, helper_start group] at hend
  calc
    (helperJump group).pc =
        UInt256.ofNat (Artifact.instructionPC (rightHelperJumpIndex (group.val + 1))) := rfl
    _ = StackRoundTrace.pcAfter (rightHelperPCOfGroup (group.val + 1))
        (rightHelperTemplate ⟨(group.val + 1), by omega⟩) := by
      fin_cases group <;> rfl
    _ = (helperSite group).endPC := hend.symm

private theorem helper_valid (group : Fin 3) :
    Decode.isValidJumpDest Artifact.code
      (rightHelperPCOfGroup (group.val + 1)).toNat = true := by
  have hpc : (rightHelperPCOfGroup (group.val + 1)).toNat =
      Artifact.instructionPC (rightHelperStartIndex (group.val + 1)) := by
    fin_cases group <;> rfl
  rw [hpc]
  exact Artifact.isValidJumpDest_index (rightHelperStartIndex (group.val + 1))
    (by fin_cases group <;> rfl)

private theorem normalReturn_valid (k : NormalIndex) :
    Decode.isValidJumpDest Artifact.code
      (rightReturnPC (normalFin k).val).toNat = true := by
  rw [show (rightReturnPC (normalFin k).val).toNat =
      Artifact.instructionPC (QuadLayout.rightReturnIndex (normalFin k).val) by
    exact (normalReturn k).pc_eq]
  exact Artifact.isValidJumpDest_index
    (QuadLayout.rightReturnIndex (normalFin k).val)
    (normalReturn k).located.atIndex

def normalRound (k : NormalIndex) :
    LoadedCalls.Normal.RoundSite Artifact .Osaka
      (rightAddress0 (normalFin k)) (rightAddress1 (normalFin k))
      (rightAddress2 (normalFin k)) (rightAddress3 (normalFin k))
      (rightRotation0 (normalFin k)) (rightRotation1 (normalFin k))
      (rightRotation2 (normalFin k)) (rightRotation3 (normalFin k))
      (LoadedHoistHelper.rightTemplate (4 - (normalFin k).val / 4) (rightConstant (normalFin k))) where
  returnPC := rightReturnPC (normalFin k).val
  helperPC := rightHelperPC (normalFin k).val
  call := normalCall k
  helper := castTemplate (helperSite ⟨(normalFin k).val / 4 - 1, by dsimp [normalFin]; omega⟩) (by fin_cases k <;> rfl)
  helper_start := by rw [castTemplate_start, helper_start]; fin_cases k <;> rfl
  helperJump := helperJump ⟨(normalFin k).val / 4 - 1, by dsimp [normalFin]; omega⟩
  helper_jump_instr := rfl
  helper_end := by rw [castTemplate_end, helper_end]
  returnSite := normalReturn k
  return_instr := rfl
  return_at := rfl
  helper_valid := by
    have h := helper_valid ⟨(normalFin k).val / 4 - 1, by dsimp [normalFin]; omega⟩
    fin_cases k <;> exact h
  return_valid := normalReturn_valid k

def fallthroughK (group : Fin 3) : Fin 20 :=
  ⟨4 * (group.val + 1) + 3, by omega⟩

private theorem fallthrough_slice (group : Fin 3) :
    (Artifact.instructions.drop (rightWrapperIndex (fallthroughK group).val)).take
        (LoadedCalls.ShiftedFallthrough.pushes
          (rightReturnPC (fallthroughK group).val)
          (rightAddress0 (fallthroughK group)) (rightAddress1 (fallthroughK group))
          (rightAddress2 (fallthroughK group)) (rightAddress3 (fallthroughK group))
          (rightRotation0 (fallthroughK group)) (rightRotation1 (fallthroughK group))
          (rightRotation2 (fallthroughK group))
          (rightRotation3 (fallthroughK group))).length =
      LoadedCalls.ShiftedFallthrough.pushes (rightReturnPC (fallthroughK group).val)
        (rightAddress0 (fallthroughK group)) (rightAddress1 (fallthroughK group))
        (rightAddress2 (fallthroughK group)) (rightAddress3 (fallthroughK group))
        (rightRotation0 (fallthroughK group)) (rightRotation1 (fallthroughK group))
        (rightRotation2 (fallthroughK group))
        (rightRotation3 (fallthroughK group)) := by
  fin_cases group <;> rfl

def fallthroughPushes (group : Fin 3) : GenericRoundSite Artifact .Osaka
    (LoadedCalls.ShiftedFallthrough.pushes (rightReturnPC (fallthroughK group).val)
      (rightAddress0 (fallthroughK group)) (rightAddress1 (fallthroughK group))
      (rightAddress2 (fallthroughK group)) (rightAddress3 (fallthroughK group))
      (rightRotation0 (fallthroughK group)) (rightRotation1 (fallthroughK group))
      (rightRotation2 (fallthroughK group))
      (rightRotation3 (fallthroughK group))) :=
  StackSiteBuilder.ofSlice _ (rightWrapperIndex (fallthroughK group).val)
    (fallthrough_slice group)
    (by fin_cases group <;> decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by fin_cases group <;> decide))
    (by simp [LoadedCalls.ShiftedFallthrough.pushes])

def fallthroughReturn (group : Fin 3) : LocatedSite Artifact .Osaka where
  located :=
    { index := QuadLayout.rightReturnIndex (fallthroughK group).val
      instruction := .op .JUMPDEST
      atIndex := by fin_cases group <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := rightReturnPC (fallthroughK group).val
  pc_eq := QuadLayout.pc_toNat_instructionPC _

private theorem fallthrough_helper_start (group : Fin 3) :
    (helperSite group).startPC = (fallthroughPushes group).endPC := by
  fin_cases group <;> rfl

private theorem fallthrough_return_valid (group : Fin 3) :
    Decode.isValidJumpDest Artifact.code
      (rightReturnPC (fallthroughK group).val).toNat = true := by
  rw [show (rightReturnPC (fallthroughK group).val).toNat =
      Artifact.instructionPC
        (QuadLayout.rightReturnIndex (fallthroughK group).val) by
    exact (fallthroughReturn group).pc_eq]
  exact Artifact.isValidJumpDest_index
    (QuadLayout.rightReturnIndex (fallthroughK group).val)
    (fallthroughReturn group).located.atIndex

def fallthroughRound (group : Fin 3) :
    LoadedCalls.Fallthrough.RoundSite Artifact .Osaka
      (rightAddress0 (fallthroughK group)) (rightAddress1 (fallthroughK group))
      (rightAddress2 (fallthroughK group)) (rightAddress3 (fallthroughK group))
      (rightRotation0 (fallthroughK group)) (rightRotation1 (fallthroughK group))
      (rightRotation2 (fallthroughK group)) (rightRotation3 (fallthroughK group))
      (LoadedHoistHelper.rightTemplate (4 - (group.val + 1)) (rightConstant (fallthroughK group))) where
  returnPC := rightReturnPC (fallthroughK group).val
  callPushes := fallthroughPushes group
  helper := castTemplate (helperSite group) (by fin_cases group <;> rfl)
  helper_start := by rw [castTemplate_start, fallthrough_helper_start]
  helperJump := helperJump group
  helper_jump_instr := rfl
  helper_end := by rw [castTemplate_end, helper_end]
  returnSite := fallthroughReturn group
  return_instr := rfl
  return_at := rfl
  return_valid := fallthrough_return_valid group

theorem normal_start (k : NormalIndex) :
    (normalRound k).call.pushes.startPC = rightPC (normalFin k).val := rfl

theorem normal_end (k : NormalIndex) :
    (normalRound k).returnSite.pc.succ =
      rightPC ((normalFin k).val + 1) := by
  fin_cases k <;> rfl

theorem fallthrough_start (group : Fin 3) :
    (fallthroughRound group).callPushes.startPC =
      rightPC (fallthroughK group).val := rfl

theorem fallthrough_end (group : Fin 3) :
    (fallthroughRound group).returnSite.pc.succ =
      rightPC ((fallthroughK group).val + 1) := by
  fin_cases group <;> rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundSitesRight
