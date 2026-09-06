import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSitesBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadCallTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskQuadHelperTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundState
open Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundTemplate
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskCallTrace
open Challenge.Ripemd160.Submission.Proofs.Bytecode.MaskHelperTemplates

private theorem leftWrapper_slice (k : Fin 20) :
    (Artifact.instructions.drop (leftWrapperIndex k.val)).take
        (leftWrapperTemplate k).length = leftWrapperTemplate k := by
  fin_cases k <;> rfl

private theorem leftWrapper_fits (k : Fin 20) :
    leftWrapperIndex k.val + (leftWrapperTemplate k).length ≤
      Artifact.instructions.length := by
  change 932 + 12 * k.val + 12 ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  omega

private theorem leftWrapper_wellFormed (k : Fin 20) :
    StackRoundData.TemplateWellFormed (leftWrapperTemplate k) := by
  fin_cases k <;> decide

def leftWrapperSite (k : Fin 20) :
    GenericRoundSite Artifact .Osaka (leftWrapperTemplate k) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka) (leftWrapperTemplate k)
    (leftWrapperIndex k.val) (leftWrapper_slice k) (leftWrapper_fits k)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (leftWrapper_wellFormed k))
    (by simp [leftWrapperTemplate, leftCallTemplate])

private theorem leftWrapperAt (k : Fin 20) (offset : Nat)
    (hoffset : offset < (leftWrapperTemplate k).length) :
    Artifact.instructions[leftWrapperIndex k.val + offset]? =
      some (leftWrapperTemplate k)[offset] :=
  getElem_of_slice _ _ (leftWrapper_slice k) _ hoffset

private theorem leftCall_slice (k : Fin 20) :
    (Artifact.instructions.drop (leftWrapperIndex k.val)).take
        (leftCallTemplate k).length = leftCallTemplate k := by
  have h := congrArg (fun xs : List Instr => xs.take 10) (leftWrapper_slice k)
  have hlen : (leftCallTemplate k).length = 10 := by
    rfl
  rw [hlen]
  simpa [leftWrapperTemplate, leftCallTemplate,
    MaskCallTrace.maskQuadCallPushes, List.take_take] using h

private theorem leftCall_fits (k : Fin 20) :
    leftWrapperIndex k.val + (leftCallTemplate k).length ≤
      Artifact.instructions.length := by
  change 932 + 12 * k.val + 10 ≤ Artifact.submissionInstructions.length
  rw [Artifact.referenceInstructions_count]
  omega

private theorem leftCall_wellFormed (k : Fin 20) :
    ∀ instruction ∈ leftCallTemplate k,
      Stepper.WellFormed .Osaka instruction := by
  intro instruction hmem
  apply StackRoundData.templateWellFormed_mem (leftWrapper_wellFormed k)
  change instruction ∈ leftCallTemplate k ++ [op .JUMP, op .JUMPDEST]
  exact List.mem_append_left _ hmem

def leftCallPushes (k : Fin 20) :
    GenericRoundSite Artifact .Osaka (leftCallTemplate k) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka)
    (leftCallTemplate k)
    (leftWrapperIndex k.val) (leftCall_slice k) (leftCall_fits k)
    QuadLayout.code_bound (leftCall_wellFormed k)
    (by simp [leftCallTemplate, MaskCallTrace.maskQuadCallPushes])

def leftCallJump (k : Fin 20) : LocatedSite Artifact .Osaka where
  located :=
    { index := leftWrapperIndex k.val + 10
      instruction := .op .JUMP
      atIndex := by
        simpa [leftWrapperTemplate, leftCallTemplate,
          MaskCallTrace.maskQuadCallPushes, op] using
          leftWrapperAt k 10 (by
            simp [leftWrapperTemplate, leftCallTemplate,
              MaskCallTrace.maskQuadCallPushes])
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := leftJumpPC k.val
  pc_eq := QuadLayout.pc_toNat_instructionPC _

private theorem leftCallPushes_end_eq (k : Fin 20) :
    (leftCallJump k).pc = (leftCallPushes k).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (leftCallPushes k).sites (leftCallPushes k).startPC
    (leftCallPushes k).endPC (leftCallPushes k).head_eq
    (leftCallPushes k).end_eq (leftCallPushes k).contiguous
  rw [(leftCallPushes k).instruction_eq] at hend
  have hstart : (leftCallPushes k).startPC = leftPC k.val := by
    rfl
  rw [hstart] at hend
  calc
    (leftCallJump k).pc = leftJumpPC k.val := by simp [leftCallJump]
    _ = StackRoundTrace.pcAfter (leftPC k.val) (leftCallTemplate k) := by
      fin_cases k <;> decide
    _ = (leftCallPushes k).endPC := hend.symm

def leftReturnSite (k : Fin 20) : LocatedSite Artifact .Osaka where
  located :=
    { index := leftWrapperIndex k.val + 11
      instruction := .op .JUMPDEST
      atIndex := by
        simpa [leftWrapperTemplate, leftCallTemplate,
          MaskCallTrace.maskQuadCallPushes, op] using
          leftWrapperAt k 11 (by
            simp [leftWrapperTemplate, leftCallTemplate,
              MaskCallTrace.maskQuadCallPushes])
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := leftReturnPC k.val
  pc_eq := QuadLayout.pc_toNat_instructionPC _

def leftCallSite (k : Fin 20) :
    MaskCallTrace.CallSite Artifact .Osaka
      (leftReturnPC k.val) (leftAddress0 k) (leftAddress1 k)
      (leftAddress2 k) (leftAddress3 k) (leftHelperPC k.val)
      (shiftedFactorWidth (leftRotation0 k))
      (shiftedFactorWidth (leftRotation1 k))
      (shiftedFactorWidth (leftRotation2 k))
      (shiftedFactorWidth (leftRotation3 k))
      (shiftedFactor (leftRotation0 k))
      (shiftedFactor (leftRotation1 k))
      (shiftedFactor (leftRotation2 k))
      (shiftedFactor (leftRotation3 k)) where
  pushes := leftCallPushes k
  jump := leftCallJump k
  jump_instr := by simp [leftCallJump]
  jump_pc := leftCallPushes_end_eq k

theorem leftCallSite_start (k : Fin 20) :
    (leftCallSite k).pushes.startPC = leftPC k.val := by
  rfl

theorem leftReturnSite_at (k : Fin 20) :
    (leftReturnSite k).pc = leftReturnPC k.val := by
  simp [leftReturnSite]

theorem leftReturnSite_succ_next (k : Fin 20) :
    (leftReturnSite k).pc.succ = leftPC (k.val + 1) := by
  fin_cases k <;> decide

private theorem leftHelper_slice (group : Fin 5) :
    (Artifact.instructions.drop (leftHelperStartIndex group.val)).take
        (leftHelperTemplate group).length = leftHelperTemplate group := by
  simpa [leftHelperTemplate] using
    (MaskHelperTemplates.leftTemplate_slice group
      (StackRoundData.leftConstant (16 * group.val)))

private theorem leftHelper_fits (group : Fin 5) :
    leftHelperStartIndex group.val + (leftHelperTemplate group).length ≤
      Artifact.instructions.length := by
  change leftHelperStartIndex group.val +
      (MaskHelperTemplates.leftTemplate group
        (StackRoundData.leftConstant (16 * group.val))).length ≤
      Artifact.submissionInstructions.length
  rw [MaskHelperTemplates.leftTemplate_length]
  rw [Artifact.referenceInstructions_count]
  fin_cases group <;> decide

private theorem leftHelper_wellFormed (group : Fin 5) :
    StackRoundData.TemplateWellFormed (leftHelperTemplate group) := by
  simpa [leftHelperTemplate] using
    (MaskHelperTemplates.leftTemplate_wellFormed group
      (StackRoundData.leftConstant (16 * group.val)))

def leftHelperSite (group : Fin 5) :
    GenericRoundSite Artifact .Osaka (leftHelperTemplate group) :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact) (fork := .Osaka) (leftHelperTemplate group)
    (leftHelperStartIndex group.val) (leftHelper_slice group) (leftHelper_fits group)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem (leftHelper_wellFormed group))
    (by
      change MaskHelperTemplates.leftTemplate group
        (StackRoundData.leftConstant (16 * group.val)) ≠ []
      exact MaskHelperTemplates.leftTemplate_nonempty group
        (StackRoundData.leftConstant (16 * group.val)))

theorem leftHelperSite_start_eq (group : Fin 5) :
    (leftHelperSite group).startPC = leftHelperPCOfGroup group.val := by
  fin_cases group <;> rfl

theorem leftHelperEndIndex (group : Fin 5) :
    leftHelperStartIndex group.val + (leftHelperTemplate group).length =
      leftHelperJumpIndex group.val := by
  change leftHelperStartIndex group.val +
      (MaskHelperTemplates.leftTemplate group
        (StackRoundData.leftConstant (16 * group.val))).length =
    leftHelperJumpIndex group.val
  rw [MaskHelperTemplates.leftTemplate_length]
  fin_cases group <;> rfl

def leftHelperJump (group : Fin 5) : LocatedSite Artifact .Osaka where
  located :=
    { index := leftHelperJumpIndex group.val
      instruction := .op .JUMP
      atIndex := by fin_cases group <;> rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.instructionPC (leftHelperJumpIndex group.val))
  pc_eq := QuadLayout.pc_toNat_instructionPC _

theorem leftHelperSite_end_eq (group : Fin 5) :
    (leftHelperJump group).pc = (leftHelperSite group).endPC := by
  have hend := StackRoundTrace.endPC_eq_pcAfter_sites
    (leftHelperSite group).sites (leftHelperSite group).startPC
    (leftHelperSite group).endPC (leftHelperSite group).head_eq
    (leftHelperSite group).end_eq (leftHelperSite group).contiguous
  rw [(leftHelperSite group).instruction_eq] at hend
  rw [leftHelperSite_start_eq group] at hend
  calc
    (leftHelperJump group).pc =
        UInt256.ofNat (Artifact.instructionPC (leftHelperJumpIndex group.val)) := by
          simp [leftHelperJump]
    _ = StackRoundTrace.pcAfter (leftHelperPCOfGroup group.val)
        (leftHelperTemplate group) := by
          fin_cases group <;> rfl
    _ = (leftHelperSite group).endPC := hend.symm

theorem leftHelper_valid (group : Fin 5) :
    Decode.isValidJumpDest Artifact.code
      (leftHelperPCOfGroup group.val).toNat = true := by
  have hpc : (leftHelperPCOfGroup group.val).toNat =
      Artifact.instructionPC (leftHelperStartIndex group.val) := by
    fin_cases group <;> rfl
  rw [hpc]
  exact Artifact.isValidJumpDest_index (leftHelperStartIndex group.val)
    (by fin_cases group <;> rfl)

theorem leftReturn_valid (k : Fin 20) :
    Decode.isValidJumpDest Artifact.code (leftReturnPC k.val).toNat = true := by
  have hpc : (leftReturnPC k.val).toNat =
      Artifact.instructionPC (leftWrapperIndex k.val + 11) := by
    exact (leftReturnSite k).pc_eq
  rw [hpc]
  exact Artifact.isValidJumpDest_index (leftWrapperIndex k.val + 11)
    (leftReturnSite k).located.atIndex

def leftRoundSite (k : Fin 20) :
    MaskQuadHelperTrace.RoundSite Artifact .Osaka
      (leftHelperTemplate ⟨k.val / 4, by omega⟩)
      (leftAddress0 k) (leftAddress1 k)
      (leftAddress2 k) (leftAddress3 k)
      (shiftedFactorWidth (leftRotation0 k))
      (shiftedFactorWidth (leftRotation1 k))
      (shiftedFactorWidth (leftRotation2 k))
      (shiftedFactorWidth (leftRotation3 k))
      (shiftedFactor (leftRotation0 k))
      (shiftedFactor (leftRotation1 k))
      (shiftedFactor (leftRotation2 k))
      (shiftedFactor (leftRotation3 k)) where
  returnPC := leftReturnPC k.val
  helperPC := leftHelperPC k.val
  call := leftCallSite k
  helper := leftHelperSite ⟨k.val / 4, by omega⟩
  helper_start := by
    exact leftHelperSite_start_eq ⟨k.val / 4, by omega⟩
  helperJump := leftHelperJump ⟨k.val / 4, by omega⟩
  helper_jump_instr := by rfl
  helper_end := by
    exact leftHelperSite_end_eq ⟨k.val / 4, by omega⟩
  returnSite := leftReturnSite k
  return_instr := by rfl
  return_at := by rfl
  helper_valid := leftHelper_valid ⟨k.val / 4, by omega⟩
  return_valid := leftReturn_valid k

theorem leftRoundSite_start (k : Fin 20) :
    (leftRoundSite k).call.pushes.startPC = leftPC k.val := by
  exact leftCallSite_start k

theorem leftRoundSite_end (k : Fin 20) :
    (leftRoundSite k).returnSite.pc.succ = leftPC (k.val + 1) := by
  exact leftReturnSite_succ_next k

theorem leftRotation0_le32 (k : Fin 20) : leftRotation0 k ≤ 32 := by
  fin_cases k <;> decide

theorem leftRotation1_le32 (k : Fin 20) : leftRotation1 k ≤ 32 := by
  fin_cases k <;> decide

theorem leftRotation2_le32 (k : Fin 20) : leftRotation2 k ≤ 32 := by
  fin_cases k <;> decide

theorem leftRotation3_le32 (k : Fin 20) : leftRotation3 k ≤ 32 := by
  fin_cases k <;> decide

@[simp] theorem leftPC_zero : leftPC 0 = UInt256.ofNat 0x53e := by rfl

@[simp] theorem leftPC_end : leftPC 20 = UInt256.ofNat 0x8e6 := by
  change UInt256.ofNat (Artifact.instructionPC (leftWrapperIndex 20)) =
    UInt256.ofNat (QuadLayout.leftWrapperPCNat 20)
  exact congrArg UInt256.ofNat (QuadLayout.leftWrapper_pc ⟨20, by decide⟩)

@[simp] theorem leftStartPC_eq : leftStartPC = UInt256.ofNat 0x53e := by rfl

@[simp] theorem leftEndPC_eq : leftEndPC = UInt256.ofNat 0x8e6 := by
  exact leftPC_end

end Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadSites
