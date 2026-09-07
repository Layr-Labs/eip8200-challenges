import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskR2Inline
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskR2Sites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate
open CachedMaskR2Inline

abbrev A := QuadSites.Artifact

-- The retained R1 return JUMPDEST is at index 2522. R2 starts after it.
theorem r2_slice :
    (A.instructions.drop 2523).take r2Code.length = r2Code := by rfl

def site : GenericRoundSite A .Osaka r2Code :=
  StackSiteBuilder.ofSlice _ 2523 r2_slice
    (by
      change 2523 + r2Code.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count, r2Code_length]
      decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide))
    (by intro h; have hlen := r2Code_length; simp [h] at hlen)

theorem start_pc : site.startPC = UInt256.ofNat 3785 := by
  change UInt256.ofNat (A.instructionPC 2523) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem end_pc : site.endPC = UInt256.ofNat 4345 := by
  have h := StackRoundTrace.endPC_eq_pcAfter_sites site.sites site.startPC site.endPC
    site.head_eq site.end_eq site.contiguous
  rw [site.instruction_eq, start_pc] at h
  exact h.trans (by decide)

-- The appended left R1 sequence starts immediately after its entry JUMPDEST.
theorem l1_slice :
    (A.instructions.drop 3643).take l1Code.length = l1Code := by rfl

def l1Site : GenericRoundSite A .Osaka l1Code :=
  StackSiteBuilder.ofSlice _ 3643 l1_slice
    (by
      change 3643 + l1Code.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count, l1Code_length]
      decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (by decide))
    (by intro h; have hlen := l1Code_length; simp [h] at hlen)

theorem l1_start_pc : l1Site.startPC = UInt256.ofNat 5373 := by
  change UInt256.ofNat (A.instructionPC 3643) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem l1_end_pc : l1Site.endPC = UInt256.ofNat 5949 := by
  have h := StackRoundTrace.endPC_eq_pcAfter_sites l1Site.sites
    l1Site.startPC l1Site.endPC l1Site.head_eq l1Site.end_eq l1Site.contiguous
  rw [l1Site.instruction_eq, l1_start_pc] at h
  exact h.trans (by decide)

def entryPush : LocatedSite A .Osaka where
  located :=
    { index := 736
      instruction := .push ⟨7, by decide⟩ (UInt256.ofNat 5372)
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := QuadLayout.leftPC 4
  pc_eq := QuadLayout.pc_toNat_instructionPC 736

def entryJump : LocatedSite A .Osaka where
  located :=
    { index := 737
      instruction := .op .JUMP
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (A.instructionPC 737)
  pc_eq := QuadLayout.pc_toNat_instructionPC 737

def entryDestination : LocatedSite A .Osaka where
  located :=
    { index := 3642
      instruction := .op .JUMPDEST
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat 5372
  pc_eq := by
    change (UInt256.ofNat 5372).toNat = A.instructionPC 3642
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide

def entryBridge : WideBridge A .Osaka where
  push := entryPush
  jump := entryJump
  destination := entryDestination
  push_instr := by rfl
  jump_instr := by rfl
  destination_instr := by rfl
  jump_at := by
    change UInt256.ofNat (A.instructionPC 737) = QuadLayout.leftPC 4 + 8
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide

def backPush : LocatedSite A .Osaka where
  located :=
    { index := 4107
      instruction := .push ⟨2, by decide⟩ (UInt256.ofNat 1479)
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (A.instructionPC 4107)
  pc_eq := QuadLayout.pc_toNat_instructionPC 4107

def backJump : LocatedSite A .Osaka where
  located :=
    { index := 4108
      instruction := .op .JUMP
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (A.instructionPC 4108)
  pc_eq := QuadLayout.pc_toNat_instructionPC 4108

def backDestination : LocatedSite A .Osaka where
  located :=
    { index := 908
      instruction := .op .JUMPDEST
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat 1479
  pc_eq := by
    change (UInt256.ofNat 1479).toNat = A.instructionPC 908
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    decide

def backBridge : CavityQuadGroup.Bridge A .Osaka where
  push := backPush
  jump := backJump
  destination := backDestination
  push_instr := by rfl
  jump_instr := by rfl
  destination_instr := by rfl
  jump_at := by
    change UInt256.ofNat (A.instructionPC 4108) =
      UInt256.ofNat (A.instructionPC 4107) + 3
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide

theorem entry_end : entryDestination.pc.succ = l1Site.startPC := by
  rw [l1_start_pc]
  decide

theorem back_start : backPush.pc = l1Site.endPC := by
  rw [l1_end_pc]
  change UInt256.ofNat (A.instructionPC 4107) = UInt256.ofNat 5949
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem back_end : backDestination.pc.succ = QuadSites.leftPC 8 := by
  change (UInt256.ofNat 1479).succ = UInt256.ofNat (A.instructionPC 909)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem start_rightPC : site.startPC = QuadSites.rightPC 8 := by
  rw [start_pc]
  change UInt256.ofNat 3785 = UInt256.ofNat (A.instructionPC _)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem end_rightPC : site.endPC = QuadSites.rightPC 12 := by
  rw [end_pc]
  change UInt256.ofNat 4345 = UInt256.ofNat (A.instructionPC _)
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

#print axioms r2_slice
#print axioms start_rightPC
#print axioms end_rightPC

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskR2Sites
