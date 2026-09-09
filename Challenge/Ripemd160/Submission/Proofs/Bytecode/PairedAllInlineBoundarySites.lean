import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedDivMaskCache
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SCanonicalStartup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate

/-- Exact schedule, startup, and tail windows of the frozen 5298-byte artifact. -/

theorem schedule_slice :
    (Artifact.submissionArtifact.instructions.drop 271).take
      PairedDivMaskCache.fullTemplate.length = PairedDivMaskCache.fullTemplate := by
  rfl

theorem schedule_instructionPC :
    Artifact.submissionArtifact.instructionPC 271 = 460 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem schedule_endInstructionPC :
    Artifact.submissionArtifact.instructionPC 433 = 721 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def scheduleSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka PairedDivMaskCache.fullTemplate :=
  StackSiteBuilder.ofSlice PairedDivMaskCache.fullTemplate 271 schedule_slice
    (by
      change 271 + PairedDivMaskCache.fullTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedDivMaskCache.fullTemplate) (by decide))
    (by decide)

theorem scheduleSite_startPC : scheduleSite.startPC = UInt256.ofNat 460 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 271) =
    UInt256.ofNat 460
  rw [schedule_instructionPC]

theorem scheduleSite_endPC : scheduleSite.endPC = UInt256.ofNat 721 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 433) = UInt256.ofNat 721
  rw [schedule_endInstructionPC]

theorem startup_slice :
    (Artifact.submissionArtifact.instructions.drop 433).take
      SCanonicalStartup.template.length = SCanonicalStartup.template := by
  rfl

theorem startup_instructionPC :
    Artifact.submissionArtifact.instructionPC 433 = 721 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem startup_endInstructionPC :
    Artifact.submissionArtifact.instructionPC 464 = 784 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def startupSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka SCanonicalStartup.template :=
  StackSiteBuilder.ofSlice SCanonicalStartup.template 433 startup_slice
    (by
      change 433 + SCanonicalStartup.template.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := SCanonicalStartup.template) (by decide))
    (by decide)

theorem startupSite_startPC : startupSite.startPC = UInt256.ofNat 721 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 433) = UInt256.ofNat 721
  rw [startup_instructionPC]

theorem startupSite_endPC : startupSite.endPC = UInt256.ofNat 784 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 464) = UInt256.ofNat 784
  rw [startup_endInstructionPC]

theorem tailPrefix_slice :
    (Artifact.submissionArtifact.instructions.drop 4133).take
      PairedAllInlineTail.prefixTemplate.length = PairedAllInlineTail.prefixTemplate := by
  rfl

theorem tailPrefix_instructionPC :
    Artifact.submissionArtifact.instructionPC 4133 = 5047 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

theorem tailPrefix_endInstructionPC :
    Artifact.submissionArtifact.instructionPC 4202 = 5131 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

def tailPrefixSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka PairedAllInlineTail.prefixTemplate :=
  StackSiteBuilder.ofSlice PairedAllInlineTail.prefixTemplate 4133 tailPrefix_slice
    (by
      change 4133 + PairedAllInlineTail.prefixTemplate.length ≤ Artifact.submissionInstructions.length
      rw [Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PairedAllInlineTail.prefixTemplate) (by decide))
    (by decide)

theorem tailPrefixSite_startPC : tailPrefixSite.startPC = UInt256.ofNat 5047 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4133) = UInt256.ofNat 5047
  rw [tailPrefix_instructionPC]

theorem tailPrefixSite_endPC : tailPrefixSite.endPC = UInt256.ofNat 5131 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4202) = UInt256.ofNat 5131
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
    { index := 4202
      instruction := .op .JUMP
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4202)
  pc_eq := instructionPC_toNat 4202

theorem tailJump_pc : tailJump.pc = UInt256.ofNat 5131 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 4202) = UInt256.ofNat 5131
  rw [tailPrefix_endInstructionPC]

def tailSite : PairedAllInlineTail.TailSite Artifact.submissionArtifact .Osaka where
  prefixSite := tailPrefixSite
  jump := tailJump
  jump_instr := rfl
  jump_pc := by rw [tailJump_pc, tailPrefixSite_endPC]

def gasSteps_schedule (s : State) (returnPC : UInt256) (p : Nat)
    (rest : List UInt256) (hstack : rest.length < 1015) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DenseScheduleTemplate.scheduleEntry s (UInt256.ofNat 460) (UInt256.ofNat p) returnPC rest)
      { s with
        pc := UInt256.ofNat 721
        stack := returnPC :: rest
        memory := PairedScheduleMemory.normalizedMemory s.memory
          (PairedScheduleData.extractedWord s.memory p)
        activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p) } := by
  have h := PairedDivMaskCache.gasSteps_fullTemplate scheduleSite s returnPC p rest
    hstack hrun hp hbound hcode hfork hnp
  simpa only [scheduleSite_startPC, scheduleSite_endPC] using h

theorem startup_resultStack (memory : ByteArray) (rho : List UInt256) :
    PairedDerivedStartup.resultStack memory rho =
      PairedStartupTrace.resultStack memory rho := by
  simp only [PairedDerivedStartup.resultStack, PairedStartupTrace.resultStack,
    PairedDerivedStartup.packedHash, PairedStartupTrace.packedHash,
    PairedDerivedStartup.lowerWord, PairedStartupTrace.lowerWord,
    PairedDerivedStartup.upperWord, PairedStartupTrace.upperWord,
    PairedDerivedStartup.pairWord, PairedStartupTrace.pairWord,
    PairedDerivedStartup.factorWord, PairedStartupTrace.factorWord]

def gasSteps_startup (s : State) (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (h32 : (MachineState.readWord s.memory 32).toNat < 2 ^ 32)
    (h64 : (MachineState.readWord s.memory 64).toNat < 2 ^ 32)
    (h96 : (MachineState.readWord s.memory 96).toNat < 2 ^ 32)
    (h128 : (MachineState.readWord s.memory 128).toNat < 2 ^ 32)
    (h160 : (MachineState.readWord s.memory 160).toNat < 2 ^ 32)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 721, stack := rho}
      {s with pc := UInt256.ofNat 784, stack := PairedStartupTrace.resultStack s.memory rho} := by
  have h := SCanonicalStartup.gasSteps_template startupSite s rho h32 h64 h96 h128 h160
    hstack hrun hactive hcode hfork hnp
  rw [startup_resultStack] at h
  change GasSteps {s with pc := startupSite.startPC, stack := rho}
    {s with pc := startupSite.endPC, stack := PairedStartupTrace.resultStack s.memory rho} at h
  simpa only [startupSite_startPC, startupSite_endPC] using h

def gasSteps_tail (s : State) (ret : UInt256) (q : PairedTailTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 1002)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 5047, stack := PairedAllInlineTail.entryStack q ret rho}
      {s with pc := ret, stack := rho, memory := PairedTailTrace.resultMemory s.memory q} := by
  have h := PairedAllInlineTail.gasSteps_tail tailSite s ret q rho hstack hrun hactive hvalid
    hcode hfork hnp
  change GasSteps {s with pc := tailPrefixSite.startPC, stack := PairedAllInlineTail.entryStack q ret rho}
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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites
