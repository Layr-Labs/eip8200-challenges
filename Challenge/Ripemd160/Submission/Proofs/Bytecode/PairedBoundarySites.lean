import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedStartupTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBoundarySites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate

/-- Exact schedule, startup, and tail windows of the frozen 5347-byte artifact. -/

theorem schedule_slice :
    (Artifact.submissionArtifact.instructions.drop 272).take
      PairedScheduleCombined.fullTemplate.length = PairedScheduleCombined.fullTemplate := by
  rfl

theorem schedule_instructionPC :
    Artifact.submissionArtifact.instructionPC 272 = 464 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem schedule_endInstructionPC :
    Artifact.submissionArtifact.instructionPC 424 = 857 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka PairedScheduleCombined.fullTemplate :=
  StackSiteBuilder.ofSlice PairedScheduleCombined.fullTemplate 272 schedule_slice
    (by
      change 272 + PairedScheduleCombined.fullTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedScheduleCombined.fullTemplate) (by decide))
    (by decide)

theorem scheduleSite_startPC : scheduleSite.startPC = UInt256.ofNat 464 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 272) =
    UInt256.ofNat 464
  rw [schedule_instructionPC]

theorem scheduleSite_endPC : scheduleSite.endPC = UInt256.ofNat 857 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 424) =
    UInt256.ofNat 857
  rw [schedule_endInstructionPC]

theorem startup_slice :
    (Artifact.submissionArtifact.instructions.drop 424).take
      PairedStartupTrace.template.length = PairedStartupTrace.template := by
  rfl

theorem startup_instructionPC :
    Artifact.submissionArtifact.instructionPC 424 = 857 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem startup_endInstructionPC :
    Artifact.submissionArtifact.instructionPC 468 = 960 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def startupSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka PairedStartupTrace.template :=
  StackSiteBuilder.ofSlice PairedStartupTrace.template 424 startup_slice
    (by
      change 424 + PairedStartupTrace.template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedStartupTrace.template) (by decide))
    (by decide)

theorem startupSite_startPC : startupSite.startPC = UInt256.ofNat 857 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 424) =
    UInt256.ofNat 857
  rw [startup_instructionPC]

theorem startupSite_endPC : startupSite.endPC = UInt256.ofNat 960 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 468) =
    UInt256.ofNat 960
  rw [startup_endInstructionPC]

theorem tailPrefix_slice :
    (Artifact.submissionArtifact.instructions.drop 3962).take
      PairedTailTrace.prefixTemplate.length = PairedTailTrace.prefixTemplate := by
  rfl

theorem tailPrefix_instructionPC :
    Artifact.submissionArtifact.instructionPC 3962 = 5083 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem tailPrefix_endInstructionPC :
    Artifact.submissionArtifact.instructionPC 4031 = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailPrefixSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka PairedTailTrace.prefixTemplate :=
  StackSiteBuilder.ofSlice PairedTailTrace.prefixTemplate 3962 tailPrefix_slice
    (by
      change 3962 + PairedTailTrace.prefixTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedTailTrace.prefixTemplate) (by decide))
    (by decide)

theorem tailPrefixSite_startPC : tailPrefixSite.startPC = UInt256.ofNat 5083 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3962) =
    UInt256.ofNat 5083
  rw [tailPrefix_instructionPC]

theorem tailPrefixSite_endPC : tailPrefixSite.endPC = UInt256.ofNat 5167 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4031) =
    UInt256.ofNat 5167
  rw [tailPrefix_endInstructionPC]

private theorem instructionPC_toNat (index : Nat) :
    (UInt256.ofNat (Artifact.submissionArtifact.instructionPC index)).toNat =
      Artifact.submissionArtifact.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt
    (Artifact.submissionArtifact.instructionPC_le_code_size index)
    StackRoundData.artifact_code_bound

def tailJump : LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := 4031
      instruction := .op .JUMP
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4031)
  pc_eq := instructionPC_toNat 4031

theorem tailJump_pc : tailJump.pc = UInt256.ofNat 5167 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4031) =
    UInt256.ofNat 5167
  rw [tailPrefix_endInstructionPC]

def tailSite : PairedTailTrace.TailSite Artifact.submissionArtifact .Osaka where
  prefixSite := tailPrefixSite
  jump := tailJump
  jump_instr := rfl
  jump_pc := by rw [tailJump_pc, tailPrefixSite_endPC]

def gasSteps_schedule (s : State) (returnPC : UInt256) (p : Nat)
    (rest : List UInt256) (hstack : rest.length < 1018) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DenseScheduleTemplate.scheduleEntry s (UInt256.ofNat 464) (UInt256.ofNat p) returnPC rest)
      { s with
        pc := UInt256.ofNat 857
        stack := returnPC :: rest
        memory := PairedScheduleMemory.normalizedMemory s.memory
          (PairedScheduleData.extractedWord s.memory p)
        activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p) } := by
  have h := PairedScheduleLift.gasSteps_fullTemplate scheduleSite s returnPC p rest
    hstack hrun hp hbound hcode hfork hnp
  simpa only [scheduleSite_startPC, scheduleSite_endPC] using h

def gasSteps_startup (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 857, stack := rho}
      {s with pc := UInt256.ofNat 960, stack := PairedStartupTrace.resultStack s.memory rho} := by
  have h := PairedStartupTrace.gasSteps_template startupSite s rho hstack hrun hactive
    hcode hfork hnp
  simpa only [startupSite_startPC, startupSite_endPC] using h

def gasSteps_tail (s : State) (ret : UInt256) (q : PairedTailTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 5083, stack := PairedTailTrace.entryStack q ret rho}
      {s with pc := ret, stack := rho, memory := PairedTailTrace.resultMemory s.memory q} := by
  have h := PairedTailTrace.gasSteps_tail tailSite s ret q rho hstack hrun hactive hvalid
    hcode hfork hnp
  change GasSteps {s with pc := tailPrefixSite.startPC, stack := PairedTailTrace.entryStack q ret rho}
    {s with pc := ret, stack := rho, memory := PairedTailTrace.resultMemory s.memory q} at h
  simpa only [tailPrefixSite_startPC] using h

#print axioms schedule_slice
#print axioms schedule_instructionPC
#print axioms schedule_endInstructionPC
#print axioms scheduleSite_startPC
#print axioms scheduleSite_endPC
#print axioms startup_slice
#print axioms startup_instructionPC
#print axioms startup_endInstructionPC
#print axioms startupSite_startPC
#print axioms startupSite_endPC
#print axioms tailPrefix_slice
#print axioms tailPrefix_instructionPC
#print axioms tailPrefix_endInstructionPC
#print axioms tailPrefixSite_startPC
#print axioms tailPrefixSite_endPC
#print axioms tailJump
#print axioms tailJump_pc
#print axioms tailSite
#print axioms gasSteps_schedule
#print axioms gasSteps_startup
#print axioms gasSteps_tail

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBoundarySites
