import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedSchedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SCanonicalStartup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineTail
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate PairedHelperBooleanTrace PairedAllInlineCoreTrace CachedCoreCommon
def scheduleTemplate : List Instr :=
  [ .op .JUMPDEST,
    .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
    .push ⟨2, by decide⟩ (UInt256.ofNat 257),
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .NOT,
    .op .DIV,
    .push ⟨3, by decide⟩ (UInt256.ofNat 65537),
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .NOT,
    .op .DIV,
    .op (.Swap ⟨2, by decide⟩),
    .op (.Dup ⟨0, by decide⟩),
    .op .MLOAD,
    .op (.Swap ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .ADD,
    .op .MLOAD,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .SHR,
    .op .XOR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 257),
    .op .MUL,
    .op .XOR,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .SHR,
    .op .XOR,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .push ⟨3, by decide⟩ (UInt256.ofNat 65537),
    .op .MUL,
    .op .XOR,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .SHR,
    .push ⟨1, by decide⟩ (UInt256.ofNat 64),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 96),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 160),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 160),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 96),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 64),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 448),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 480),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 8),
    .op .SHR,
    .op .XOR,
    .op (.Dup ⟨2, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 257),
    .op .MUL,
    .op .XOR,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 16),
    .op .SHR,
    .op .XOR,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .push ⟨3, by decide⟩ (UInt256.ofNat 65537),
    .op .MUL,
    .op .XOR,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 224),
    .op .SHR,
    .push ⟨0, by decide⟩ (UInt256.ofNat 0),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 192),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .MSTORE,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 160),
    .op .SHR,
    .op (.Dup ⟨3, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 256),
    .op .MSTORE,
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHR,
    .op (.Dup ⟨4, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 288),
    .op .MSTORE,
    .push ⟨1, by decide⟩ (UInt256.ofNat 22),
    .op (.Dup ⟨2, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 96),
    .op .SHR,
    .op (.Dup ⟨5, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 320),
    .op .MSTORE,
    .op (.Dup ⟨3, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 64),
    .op .SHR,
    .op (.Dup ⟨6, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 352),
    .op .MSTORE,
    .op (.Dup ⟨4, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 32),
    .op .SHR,
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 384),
    .op .MSTORE,
    .op (.Swap ⟨4, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .op .AND,
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨2, by decide⟩ (UInt256.ofNat 416),
    .op .MSTORE,
    .op (.Swap ⟨5, by decide⟩),
    .op .POP,
    .op (.Swap ⟨5, by decide⟩),
    .op .POP,
    .op (.Swap ⟨5, by decide⟩),
    .op .POP ]
theorem schedule_slice :
    (Artifact.submissionArtifact.instructions.drop 292).take scheduleTemplate.length = scheduleTemplate := by rfl
def scheduleSite : GenericRoundSite Artifact.submissionArtifact .Osaka scheduleTemplate :=
  StackSiteBuilder.ofSlice scheduleTemplate 292 schedule_slice
    (by change 292 + scheduleTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := scheduleTemplate) (by decide))
    (by decide)
theorem schedule_pc : scheduleSite.startPC = UInt256.ofNat 478 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 292) = UInt256.ofNat 478
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem schedule_advances {instruction : Instr} (hmem : instruction ∈ scheduleTemplate)
    {s t : State} (hr : Stepper.runInstr instruction s = some t) :
    t.pc = s.pc + UInt256.ofNat instruction.size := by
  have heq : scheduleTemplate = PairedDivMaskCache.cachedInitial ++
      ((PairedMask32Cache.upperTemplate ++ CachedSchedule.lowerEndian) ++ CachedSchedule.actualLower) := by rfl
  rw [heq] at hmem
  rcases List.mem_append.mp hmem with hi | hrm
  · have hm : instruction ∈ PairedDivMaskCache.fullTemplate := by
      simp only [PairedDivMaskCache.fullTemplate, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hi)))
    rcases PairedDivMaskCache.fullTemplate_advances instruction hm with hn | hd
    · exact DenseScheduleLift.runInstr_pc_of_advances hn hr
    · subst instruction
      exact PairedDivMaskCache.runInstr_pc_div hr
  · have hall : ∀ i ∈ ((PairedMask32Cache.upperTemplate ++ CachedSchedule.lowerEndian) ++ CachedSchedule.actualLower),
        DenseScheduleLift.Advances i := by
      apply coreAdvancesAll_sound
      decide
    exact DenseScheduleLift.runInstr_pc_of_advances (hall instruction hrm) hr
theorem schedule_eq : scheduleTemplate = CachedSchedule.fullTemplate := by rfl
def gasSteps_schedule (s : State) (returnPC : UInt256) (p : Nat)
    (rest : List UInt256) (hstack : rest.length ≤ 996) (hrun : s.halt = .Running)
    (hp : 736 ≤ p) (hbound : p + 64 < 2 ^ 256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hsentinel : SentinelCore.SentinelOK s.memory) :
    GasSteps (DenseScheduleTemplate.scheduleEntry s (UInt256.ofNat 478) (UInt256.ofNat p) returnPC rest)
      {s with pc := UInt256.ofNat 712, stack := cache (PairedScheduleMemory.normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p)) ++ (returnPC :: rest), memory := PairedScheduleMemory.normalizedMemory s.memory (PairedScheduleData.extractedWord s.memory p), activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat p)} := by
  have h := CachedSchedule.run_fullTemplate_natural s returnPC p rest hstack hrun hp hbound hsentinel
  have hpct : pcAfter (UInt256.ofNat 478) CachedSchedule.fullTemplate = UInt256.ofNat 712 := by rfl
  rw [hpct] at h
  have hl := runLocatedBlock_eq_runInstrSeq_site scheduleSite
    (DenseScheduleTemplate.scheduleEntry s (UInt256.ofNat 478) (UInt256.ofNat p) returnPC rest)
    schedule_pc.symm (by
      intro located hm u v hr
      apply schedule_advances ?_ hr
      rw [← scheduleSite.instruction_eq]
      exact List.mem_map_of_mem hm)
  rw [← schedule_eq] at h
  rw [h] at hl
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka scheduleSite.path
    hcode hfork hl hrun hnp
def startupTemplate : List Instr :=
  [ .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295),
    .op (.Dup ⟨0, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHL,
    .op (.Dup ⟨0, by decide⟩),
    .op (.Dup ⟨2, by decide⟩),
    .op .OR,
    .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .op .DIV,
    .push ⟨2, by decide⟩ (UInt256.ofNat 672),
    .op .MLOAD,
    .op (.Dup ⟨1, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 640),
    .op .MLOAD,
    .op (.Dup ⟨2, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 608),
    .op .MLOAD,
    .op (.Dup ⟨3, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MLOAD,
    .op (.Dup ⟨4, by decide⟩),
    .op .MUL,
    .push ⟨2, by decide⟩ (UInt256.ofNat 544),
    .op .MLOAD,
    .op (.Dup ⟨5, by decide⟩),
    .op .MUL,
    .push ⟨5, by decide⟩ (UInt256.ofNat 4294967297),
    .op (.Swap ⟨5, by decide⟩),
    .op .POP ]
theorem startup_slice :
    (Artifact.submissionArtifact.instructions.drop 465).take startupTemplate.length = startupTemplate := by rfl
def startupSite : GenericRoundSite Artifact.submissionArtifact .Osaka startupTemplate :=
  StackSiteBuilder.ofSlice startupTemplate 465 startup_slice
    (by change 465 + startupTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := startupTemplate) (by decide))
    (by decide)
theorem startup_pc : startupSite.startPC = UInt256.ofNat 713 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 465) = UInt256.ofNat 713
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem startup_endPC : startupSite.endPC = UInt256.ofNat 766 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 498) = UInt256.ofNat 766
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
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
    (h32 : (MachineState.readWord s.memory 544).toNat < 2 ^ 32)
    (h64 : (MachineState.readWord s.memory 576).toNat < 2 ^ 32)
    (h96 : (MachineState.readWord s.memory 608).toNat < 2 ^ 32)
    (h128 : (MachineState.readWord s.memory 640).toNat < 2 ^ 32)
    (h160 : (MachineState.readWord s.memory 672).toNat < 2 ^ 32)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 713, stack := rho}
      {s with pc := UInt256.ofNat 766, stack := PairedStartupTrace.resultStack s.memory rho} := by
  have h := SCanonicalStartup.gasSteps_template startupSite s rho h32 h64 h96 h128 h160
    hstack hrun hactive hcode hfork hnp
  rw [startup_resultStack] at h
  change GasSteps {s with pc := startupSite.startPC, stack := rho}
    {s with pc := startupSite.endPC, stack := PairedStartupTrace.resultStack s.memory rho} at h
  simpa only [startup_pc, startup_endPC] using h

def cachedTailEntry (memory : ByteArray) (q : PairedTailTrace.Frame) (ret : UInt256) (rho : List UInt256) : List UInt256 :=
  [q.d, q.b, q.c, q.a, q.e, q.unused5, q.unused6, q.unused3, q.lower] ++ (cache memory ++ (ret :: rho))
def tailTemplate : List Instr :=
  [ .op (.Dup ⟨2, by decide⟩),
    .op (.Dup ⟨1, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨9, by decide⟩),
    .op .AND,
    .op (.Dup ⟨1, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 608),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨10, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op (.Dup ⟨6, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 640),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨11, by decide⟩),
    .op .AND,
    .op (.Dup ⟨6, by decide⟩),
    .op (.Dup ⟨5, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 672),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨12, by decide⟩),
    .op .AND,
    .op (.Dup ⟨5, by decide⟩),
    .op (.Dup ⟨7, by decide⟩),
    .push ⟨1, by decide⟩ (UInt256.ofNat 128),
    .op .SHR,
    .op .ADD,
    .push ⟨2, by decide⟩ (UInt256.ofNat 544),
    .op .MLOAD,
    .op .ADD,
    .op (.Dup ⟨13, by decide⟩),
    .op .AND,
    .push ⟨2, by decide⟩ (UInt256.ofNat 672),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 640),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 608),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 576),
    .op .MSTORE,
    .push ⟨2, by decide⟩ (UInt256.ofNat 544),
    .op .MSTORE,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .POP,
    .op .JUMP ]
theorem tail_slice :
    (Artifact.submissionArtifact.instructions.drop 3938).take tailTemplate.length = tailTemplate := by rfl
def tailSite : GenericRoundSite Artifact.submissionArtifact .Osaka tailTemplate :=
  StackSiteBuilder.ofSlice tailTemplate 3938 tail_slice
    (by change 3938 + tailTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem (instructions := tailTemplate) (by decide))
    (by decide)
theorem tail_pc : tailSite.startPC = UInt256.ofNat 4610 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3938) = UInt256.ofNat 4610
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem tail_advances : ∀ instruction ∈ tailTemplate.dropLast, DenseScheduleLift.Advances instruction := by
  apply coreAdvancesAll_sound
  decide
theorem run_tail (s : State) (ret : UInt256) (q : PairedTailTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true) :
    runInstrSeq tailTemplate {s with pc := UInt256.ofNat 4610, stack := cachedTailEntry s.memory q ret rho} =
      some {s with pc := ret, stack := rho, memory := PairedTailTrace.resultMemory s.memory q} := by
  have hcap (n : Nat) (hn : n ≤ 26) : rho.length + n < 1024 := by omega
  have hactiveAt (address : Nat) (haddress : address ≤ 672) :
      UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat address 32) = s.activeWords :=
    PairedStartupTrace.active_preserved s.activeWords address hactive haddress
  simp (discharger := omega) [tailTemplate, cachedTailEntry, cache, PairedTailTrace.combine,
    PairedTailTrace.result0, PairedTailTrace.result1, PairedTailTrace.result2,
    PairedTailTrace.result3, PairedTailTrace.result4, PairedTailTrace.resultMemory, PairedTailTrace.writeWord,
    runInstrSeq, Stepper.runInstr, UInt256.succ, Instr.size, List.getElem?_cons_zero,
    hrun, hcap, Nat.add_assoc, State.activeWordsAfterUInt256, hactiveAt, hvalid,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  all_goals repeat first | apply And.intro | rfl

def gasSteps_tail (s : State) (ret : UInt256) (q : PairedTailTrace.Frame)
    (rho : List UInt256) (hstack : rho.length ≤ 996)
    (hrun : s.halt = .Running) (hactive : 23 ≤ s.activeWords.toNat)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code ret.toNat = true)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4610, stack := cachedTailEntry s.memory q ret rho}
      {s with pc := ret, stack := rho, memory := PairedTailTrace.resultMemory s.memory q} := by
  exact gasSteps_terminal_of_raw tailSite _ _ hcode hfork hrun hnp tail_pc.symm tail_advances
    (run_tail s ret q rho hstack hrun hactive hvalid)
#print axioms gasSteps_schedule
#print axioms gasSteps_tail
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedAllInlineBoundarySites
