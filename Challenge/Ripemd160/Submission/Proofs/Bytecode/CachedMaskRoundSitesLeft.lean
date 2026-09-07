import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadHelperTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoadedCalls
import Challenge.Ripemd160.Submission.Proofs.Bytecode.LoadedHoistHelper

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundSitesLeft

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

abbrev Artifact := QuadSites.Artifact

abbrev NormalIndex := Fin 3

def groupFin (group : Fin 2) : Fin 5 :=
  ⟨3, by decide⟩

def normalGroup (k : NormalIndex) : Fin 2 :=
  ⟨0, by decide⟩

def normalFin (k : NormalIndex) : Fin 20 :=
  ⟨4 * (groupFin (normalGroup k)).val + k.val % 3, by
    have h := (groupFin (normalGroup k)).isLt
    omega⟩

private theorem normal_slice (k : NormalIndex) :
    (Artifact.instructions.drop (leftWrapperIndex (normalFin k).val)).take
        (LoadedCalls.ShiftedCall.quadCallPushes (leftReturnPC (normalFin k).val)
          (leftAddress0 (normalFin k)) (leftAddress1 (normalFin k))
          (leftAddress2 (normalFin k)) (leftAddress3 (normalFin k))
          (leftHelperPC (normalFin k).val) (leftRotation0 (normalFin k))
          (leftRotation1 (normalFin k)) (leftRotation2 (normalFin k))
          (leftRotation3 (normalFin k))).length =
      LoadedCalls.ShiftedCall.quadCallPushes (leftReturnPC (normalFin k).val)
        (leftAddress0 (normalFin k)) (leftAddress1 (normalFin k))
        (leftAddress2 (normalFin k)) (leftAddress3 (normalFin k))
        (leftHelperPC (normalFin k).val) (leftRotation0 (normalFin k))
        (leftRotation1 (normalFin k)) (leftRotation2 (normalFin k))
        (leftRotation3 (normalFin k)) := by
  fin_cases k <;>
    simp only [normalFin, leftReturnPC, QuadLayout.leftReturnPC,
      ArtifactByteLength.instructionPC_eq_byteLength] <;> rfl

private theorem normal_fits (k : NormalIndex) :
    leftWrapperIndex (normalFin k).val +
        (LoadedCalls.ShiftedCall.quadCallPushes (leftReturnPC (normalFin k).val)
          (leftAddress0 (normalFin k)) (leftAddress1 (normalFin k))
          (leftAddress2 (normalFin k)) (leftAddress3 (normalFin k))
          (leftHelperPC (normalFin k).val) (leftRotation0 (normalFin k))
          (leftRotation1 (normalFin k)) (leftRotation2 (normalFin k))
          (leftRotation3 (normalFin k))).length ≤
      Artifact.instructions.length := by
  fin_cases k <;> decide

private theorem normal_wellFormed (k : NormalIndex) :
    ∀ instruction ∈ LoadedCalls.ShiftedCall.quadCallPushes
        (leftReturnPC (normalFin k).val)
        (leftAddress0 (normalFin k)) (leftAddress1 (normalFin k))
        (leftAddress2 (normalFin k)) (leftAddress3 (normalFin k))
        (leftHelperPC (normalFin k).val) (leftRotation0 (normalFin k))
        (leftRotation1 (normalFin k)) (leftRotation2 (normalFin k))
        (leftRotation3 (normalFin k)),
      Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  exact StackRoundData.templateWellFormed_mem (by
    fin_cases k <;> decide) instruction hmem

def normalPushes (k : NormalIndex) :
    GenericRoundSite Artifact .Osaka
      (LoadedCalls.ShiftedCall.quadCallPushes (leftReturnPC (normalFin k).val)
        (leftAddress0 (normalFin k)) (leftAddress1 (normalFin k))
        (leftAddress2 (normalFin k)) (leftAddress3 (normalFin k))
        (leftHelperPC (normalFin k).val) (leftRotation0 (normalFin k))
        (leftRotation1 (normalFin k)) (leftRotation2 (normalFin k))
        (leftRotation3 (normalFin k))) :=
  StackSiteBuilder.ofSlice _ (leftWrapperIndex (normalFin k).val) (normal_slice k)
    (normal_fits k) QuadLayout.code_bound (normal_wellFormed k)
    (by simp [LoadedCalls.ShiftedCall.quadCallPushes])

def normalJump (k : NormalIndex) : LocatedSite Artifact .Osaka where
  located :=
    { index := leftWrapperIndex (normalFin k).val + 15
      instruction := .op .JUMP
      atIndex := by
        fin_cases k <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := leftJumpPC (normalFin k).val
  pc_eq := QuadLayout.pc_toNat_instructionPC _

private theorem normalPushes_end (k : NormalIndex) :
    (normalJump k).pc = (normalPushes k).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (normalPushes k).sites (normalPushes k).startPC (normalPushes k).endPC
    (normalPushes k).head_eq (normalPushes k).end_eq
    (normalPushes k).contiguous
  rw [(normalPushes k).instruction_eq] at hend
  have hstart : (normalPushes k).startPC = leftPC (normalFin k).val := by rfl
  rw [hstart] at hend
  calc
    (normalJump k).pc = leftJumpPC (normalFin k).val := by rfl
    _ = StackRoundTrace.pcAfter (leftPC (normalFin k).val)
        (LoadedCalls.ShiftedCall.quadCallPushes (leftReturnPC (normalFin k).val)
          (leftAddress0 (normalFin k)) (leftAddress1 (normalFin k))
          (leftAddress2 (normalFin k)) (leftAddress3 (normalFin k))
          (leftHelperPC (normalFin k).val) (leftRotation0 (normalFin k))
          (leftRotation1 (normalFin k)) (leftRotation2 (normalFin k))
          (leftRotation3 (normalFin k))) := by
      fin_cases k <;>
        simp only [normalFin, leftPC, leftJumpPC, leftReturnPC,
          QuadLayout.leftPC, QuadLayout.leftJumpPC,
          QuadLayout.leftReturnPC,
          ArtifactByteLength.instructionPC_eq_byteLength] <;> rfl
    _ = (normalPushes k).endPC := hend.symm

def normalReturn (k : NormalIndex) : LocatedSite Artifact .Osaka where
  located :=
    { index := QuadLayout.leftReturnIndex (normalFin k).val
      instruction := .op .JUMPDEST
      atIndex := by
        fin_cases k <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := leftReturnPC (normalFin k).val
  pc_eq := QuadLayout.pc_toNat_instructionPC _

def normalCall (k : NormalIndex) :
    LoadedCalls.ShiftedCall.CallSite Artifact .Osaka
      (leftReturnPC (normalFin k).val)
      (leftAddress0 (normalFin k)) (leftAddress1 (normalFin k))
      (leftAddress2 (normalFin k)) (leftAddress3 (normalFin k))
      (leftHelperPC (normalFin k).val)
      (leftRotation0 (normalFin k)) (leftRotation1 (normalFin k))
      (leftRotation2 (normalFin k)) (leftRotation3 (normalFin k)) where
  pushes := normalPushes k
  jump := normalJump k
  jump_instr := rfl
  jump_pc := normalPushes_end k

private theorem helper_slice (group : Fin 2) :
    (Artifact.instructions.drop (leftHelperStartIndex (groupFin group).val)).take
        (leftHelperTemplate (groupFin group)).length = leftHelperTemplate (groupFin group) := by
  fin_cases group <;> rfl

def helperSite (group : Fin 2) :
    GenericRoundSite Artifact .Osaka (leftHelperTemplate (groupFin group)) :=
  StackSiteBuilder.ofSlice _ (leftHelperStartIndex (groupFin group).val)
    (helper_slice group)
    (by fin_cases group <;> decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by fin_cases group <;> decide))
    (by fin_cases group <;> decide)

def helperJump (group : Fin 2) : LocatedSite Artifact .Osaka where
  located :=
    { index := leftHelperJumpIndex (groupFin group).val
      instruction := .op .JUMP
      atIndex := by fin_cases group <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.instructionPC (leftHelperJumpIndex (groupFin group).val))
  pc_eq := QuadLayout.pc_toNat_instructionPC _

private theorem helper_start (group : Fin 2) :
    (helperSite group).startPC = leftHelperPCOfGroup (groupFin group).val := by
  fin_cases group <;> rfl

private theorem helper_end (group : Fin 2) :
    (helperJump group).pc = (helperSite group).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (helperSite group).sites (helperSite group).startPC (helperSite group).endPC
    (helperSite group).head_eq (helperSite group).end_eq
    (helperSite group).contiguous
  rw [(helperSite group).instruction_eq, helper_start group] at hend
  calc
    (helperJump group).pc =
        UInt256.ofNat (Artifact.instructionPC (leftHelperJumpIndex (groupFin group).val)) := rfl
    _ = StackRoundTrace.pcAfter (leftHelperPCOfGroup (groupFin group).val)
        (leftHelperTemplate (groupFin group)) := by
      fin_cases group <;> rfl
    _ = (helperSite group).endPC := hend.symm

private theorem helper_valid (group : Fin 2) :
    Decode.isValidJumpDest Artifact.code
      (leftHelperPCOfGroup (groupFin group).val).toNat = true := by
  have hpc : (leftHelperPCOfGroup (groupFin group).val).toNat =
      Artifact.instructionPC (leftHelperStartIndex (groupFin group).val) := by
    fin_cases group <;> rfl
  rw [hpc]
  exact Artifact.isValidJumpDest_index (leftHelperStartIndex (groupFin group).val)
    (by fin_cases group <;> rfl)

private theorem normalReturn_valid (k : NormalIndex) :
    Decode.isValidJumpDest Artifact.code
      (leftReturnPC (normalFin k).val).toNat = true := by
  rw [show (leftReturnPC (normalFin k).val).toNat =
      Artifact.instructionPC (QuadLayout.leftReturnIndex (normalFin k).val) by
    exact (normalReturn k).pc_eq]
  exact Artifact.isValidJumpDest_index
    (QuadLayout.leftReturnIndex (normalFin k).val)
    (normalReturn k).located.atIndex

def normalRound (k : NormalIndex) :
    LoadedCalls.Normal.RoundSite Artifact .Osaka
      (leftAddress0 (normalFin k)) (leftAddress1 (normalFin k))
      (leftAddress2 (normalFin k)) (leftAddress3 (normalFin k))
      (leftRotation0 (normalFin k)) (leftRotation1 (normalFin k))
      (leftRotation2 (normalFin k)) (leftRotation3 (normalFin k))
      (LoadedHoistHelper.leftTemplate ((normalFin k).val / 4) (leftConstant (normalFin k))) where
  returnPC := leftReturnPC (normalFin k).val
  helperPC := leftHelperPC (normalFin k).val
  call := normalCall k
  helper := castTemplate (helperSite (normalGroup k)) (by fin_cases k <;> rfl)
  helper_start := by rw [castTemplate_start, helper_start]; fin_cases k <;> rfl
  helperJump := helperJump (normalGroup k)
  helper_jump_instr := rfl
  helper_end := by rw [castTemplate_end, helper_end]
  returnSite := normalReturn k
  return_instr := rfl
  return_at := rfl
  helper_valid := by
    have h := helper_valid (normalGroup k)
    convert h using 1; fin_cases k <;> rfl
  return_valid := normalReturn_valid k

def fallthroughK (group : Fin 2) : Fin 20 :=
  ⟨4 * (groupFin group).val + 3, by have h := (groupFin group).isLt; omega⟩

private theorem fallthrough_slice (group : Fin 2) :
    (Artifact.instructions.drop (leftWrapperIndex (fallthroughK group).val)).take
        (LoadedCalls.ShiftedFallthrough.pushes
          (leftReturnPC (fallthroughK group).val)
          (leftAddress0 (fallthroughK group)) (leftAddress1 (fallthroughK group))
          (leftAddress2 (fallthroughK group)) (leftAddress3 (fallthroughK group))
          (leftRotation0 (fallthroughK group)) (leftRotation1 (fallthroughK group))
          (leftRotation2 (fallthroughK group))
          (leftRotation3 (fallthroughK group))).length =
      LoadedCalls.ShiftedFallthrough.pushes (leftReturnPC (fallthroughK group).val)
        (leftAddress0 (fallthroughK group)) (leftAddress1 (fallthroughK group))
        (leftAddress2 (fallthroughK group)) (leftAddress3 (fallthroughK group))
        (leftRotation0 (fallthroughK group)) (leftRotation1 (fallthroughK group))
        (leftRotation2 (fallthroughK group))
        (leftRotation3 (fallthroughK group)) := by
  fin_cases group <;> rfl

def fallthroughPushes (group : Fin 2) : GenericRoundSite Artifact .Osaka
    (LoadedCalls.ShiftedFallthrough.pushes (leftReturnPC (fallthroughK group).val)
      (leftAddress0 (fallthroughK group)) (leftAddress1 (fallthroughK group))
      (leftAddress2 (fallthroughK group)) (leftAddress3 (fallthroughK group))
      (leftRotation0 (fallthroughK group)) (leftRotation1 (fallthroughK group))
      (leftRotation2 (fallthroughK group))
      (leftRotation3 (fallthroughK group))) :=
  StackSiteBuilder.ofSlice _ (leftWrapperIndex (fallthroughK group).val)
    (fallthrough_slice group)
    (by fin_cases group <;> decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by fin_cases group <;> decide))
    (by simp [LoadedCalls.ShiftedFallthrough.pushes])

def fallthroughReturn (group : Fin 2) : LocatedSite Artifact .Osaka where
  located :=
    { index := QuadLayout.leftReturnIndex (fallthroughK group).val
      instruction := .op .JUMPDEST
      atIndex := by fin_cases group <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := leftReturnPC (fallthroughK group).val
  pc_eq := QuadLayout.pc_toNat_instructionPC _

private theorem fallthrough_helper_start (group : Fin 2) :
    (helperSite group).startPC = (fallthroughPushes group).endPC := by
  fin_cases group <;> rfl

private theorem fallthrough_return_valid (group : Fin 2) :
    Decode.isValidJumpDest Artifact.code
      (leftReturnPC (fallthroughK group).val).toNat = true := by
  rw [show (leftReturnPC (fallthroughK group).val).toNat =
      Artifact.instructionPC
        (QuadLayout.leftReturnIndex (fallthroughK group).val) by
    exact (fallthroughReturn group).pc_eq]
  exact Artifact.isValidJumpDest_index
    (QuadLayout.leftReturnIndex (fallthroughK group).val)
    (fallthroughReturn group).located.atIndex

def fallthroughRound (group : Fin 2) :
    LoadedCalls.Fallthrough.RoundSite Artifact .Osaka
      (leftAddress0 (fallthroughK group)) (leftAddress1 (fallthroughK group))
      (leftAddress2 (fallthroughK group)) (leftAddress3 (fallthroughK group))
      (leftRotation0 (fallthroughK group)) (leftRotation1 (fallthroughK group))
      (leftRotation2 (fallthroughK group)) (leftRotation3 (fallthroughK group))
      (LoadedHoistHelper.leftTemplate ((groupFin group).val) (leftConstant (fallthroughK group))) where
  returnPC := leftReturnPC (fallthroughK group).val
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
    (normalRound k).call.pushes.startPC = leftPC (normalFin k).val := rfl

theorem normal_end (k : NormalIndex) :
    (normalRound k).returnSite.pc.succ =
      leftPC ((normalFin k).val + 1) := by
  fin_cases k <;> rfl

theorem fallthrough_start (group : Fin 2) :
    (fallthroughRound group).callPushes.startPC =
      leftPC (fallthroughK group).val := rfl

theorem fallthrough_end (group : Fin 2) :
    (fallthroughRound group).returnSite.pc.succ =
      leftPC ((fallthroughK group).val + 1) := by
  fin_cases group <;> rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskRoundSitesLeft
