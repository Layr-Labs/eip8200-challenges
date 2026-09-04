import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackPC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.EvmProof
open StackRoundTemplate

open private submissionInstructionsChunk0 submissionInstructionsChunk1
  submissionInstructionsChunk2 submissionInstructionsChunk3
  submissionInstructionsChunk4 submissionInstructionsChunk5
  submissionInstructionsChunk6 submissionInstructionsChunk7
  submissionInstructionsChunk8 submissionInstructionsChunk9
  submissionInstructionsChunk10 submissionInstructionsChunk11
  submissionInstructionsChunk12 submissionInstructionsChunk13
  submissionInstructionsChunk0_length submissionInstructionsChunk1_length
  submissionInstructionsChunk2_length submissionInstructionsChunk3_length
  submissionInstructionsChunk4_length submissionInstructionsChunk5_length
  submissionInstructionsChunk6_length submissionInstructionsChunk7_length
  submissionInstructionsChunk8_length submissionInstructionsChunk9_length
  submissionInstructionsChunk10_length submissionInstructionsChunk11_length
  submissionInstructionsChunk12_length submissionInstructionsChunk13_length
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

private theorem advances_straight {instruction : Instr}
    (h : StraightLine instruction) : PackedScheduleLift.Advances instruction := by
  exact Or.inl (Or.inl h)

private theorem advances_jumpdest :
    PackedScheduleLift.Advances (.op .JUMPDEST) := by
  exact Or.inl (Or.inr (Or.inr rfl))

private theorem advances_mstore :
    PackedScheduleLift.Advances (.op .MSTORE) := by
  exact Or.inr rfl

private theorem initialTemplate_advances :
    ∀ instruction ∈ PackedScheduleTemplate.initialTemplate,
      PackedScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [PackedScheduleTemplate.initialTemplate, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact advances_jumpdest
  all_goals exact advances_straight (by constructor)

private theorem endianStage_advances (shift : Nat) (mask : UInt256) :
    ∀ instruction ∈ PackedScheduleTemplate.endianStage shift mask,
      PackedScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [PackedScheduleTemplate.endianStage, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact advances_straight (by constructor)

private theorem storeJ0_advances (half : Nat) :
    ∀ instruction ∈ PackedScheduleTemplate.storeJ0 half,
      PackedScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [PackedScheduleTemplate.storeJ0, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_mstore

private theorem storeJ_advances (half index : Nat) :
    ∀ instruction ∈ PackedScheduleTemplate.storeJ half index,
      PackedScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [PackedScheduleTemplate.storeJ, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_mstore

private theorem storeJ7_advances (half : Nat) :
    ∀ instruction ∈ PackedScheduleTemplate.storeJ7 half,
      PackedScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [PackedScheduleTemplate.storeJ7, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_straight (by constructor)
  · exact advances_mstore

private theorem storeTemplate_advances (half : Nat) :
    ∀ instruction ∈ PackedScheduleTemplate.storeTemplate half,
      PackedScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [PackedScheduleTemplate.storeTemplate, List.mem_append] at hmem
  rcases hmem with ((((((h0 | h1) | h2) | h3) | h4) | h5) | h6) | h7
  · exact storeJ0_advances half instruction h0
  · exact storeJ_advances half 1 instruction h1
  · exact storeJ_advances half 2 instruction h2
  · exact storeJ_advances half 3 instruction h3
  · exact storeJ_advances half 4 instruction h4
  · exact storeJ_advances half 5 instruction h5
  · exact storeJ_advances half 6 instruction h6
  · exact storeJ7_advances half instruction h7

private theorem halfTemplate_advances (half : Nat) :
    ∀ instruction ∈ PackedScheduleTemplate.halfTemplate half,
      PackedScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [PackedScheduleTemplate.halfTemplate, List.mem_append] at hmem
  rcases hmem with (h8 | h16) | hstore
  · exact endianStage_advances 8 PackedScheduleTemplate.mask8 instruction h8
  · exact endianStage_advances 16 PackedScheduleTemplate.mask16 instruction h16
  · exact storeTemplate_advances half instruction hstore

theorem ascendingPackedTemplate_advances :
    ∀ instruction ∈ PackedScheduleTemplate.ascendingPackedTemplate,
      PackedScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [PackedScheduleTemplate.ascendingPackedTemplate, List.mem_append] at hmem
  rcases hmem with (hinitial | h0) | h1
  · exact initialTemplate_advances instruction hinitial
  · exact halfTemplate_advances 0 instruction h0
  · exact halfTemplate_advances 1 instruction h1

private def packedSchedulePrefix : List Instr :=
  submissionInstructionsChunk0 ++ submissionInstructionsChunk1 ++
    submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++
    submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++
    submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++
    submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++
    submissionInstructionsChunk10 ++ submissionInstructionsChunk11 ++
    []

private theorem packedSchedulePrefix_length : packedSchedulePrefix.length = 2400 := by
  simp [packedSchedulePrefix]

private def packedScheduleBefore : List Instr :=
  packedSchedulePrefix ++ submissionInstructionsChunk12.take 55

private theorem packedScheduleBefore_length : packedScheduleBefore.length = 2455 := by
  simp [packedScheduleBefore, packedSchedulePrefix_length]

private theorem artifact_prefix_split :
    Artifact.submissionArtifact.instructions =
      packedSchedulePrefix ++
        (submissionInstructionsChunk12 ++ submissionInstructionsChunk13) := by
  change Artifact.submissionInstructions =
    packedSchedulePrefix ++
      (submissionInstructionsChunk12 ++ submissionInstructionsChunk13)
  simp only [Artifact.submissionInstructions, packedSchedulePrefix, List.append_assoc,
    List.nil_append]

private theorem artifact_tail_split :
    submissionInstructionsChunk12 ++ submissionInstructionsChunk13 =
      submissionInstructionsChunk12.take 55 ++
        PackedScheduleTemplate.ascendingPackedFullTemplate := by
  have hdrop : submissionInstructionsChunk12.drop 55 ++ submissionInstructionsChunk13 =
      PackedScheduleTemplate.ascendingPackedFullTemplate := by
    rfl
  calc
    submissionInstructionsChunk12 ++ submissionInstructionsChunk13 =
        (submissionInstructionsChunk12.take 55 ++
          submissionInstructionsChunk12.drop 55) ++ submissionInstructionsChunk13 := by
      rw [List.take_append_drop]
    _ = submissionInstructionsChunk12.take 55 ++
        (submissionInstructionsChunk12.drop 55 ++ submissionInstructionsChunk13) := by
      simp only [List.append_assoc]
    _ = submissionInstructionsChunk12.take 55 ++
        PackedScheduleTemplate.ascendingPackedFullTemplate := by rw [hdrop]

private theorem artifact_packed_split :
    Artifact.submissionArtifact.instructions =
      packedScheduleBefore ++ PackedScheduleTemplate.ascendingPackedFullTemplate := by
  rw [artifact_prefix_split, artifact_tail_split]
  simp [packedScheduleBefore, List.append_assoc]

private theorem artifact_packed_split_prejump :
    Artifact.submissionArtifact.instructions =
      packedScheduleBefore ++ PackedScheduleTemplate.ascendingPackedTemplate ++
        PackedScheduleTemplate.finalJumpTemplate := by
  simpa [PackedScheduleTemplate.ascendingPackedFullTemplate, List.append_assoc] using
    artifact_packed_split

private theorem instructionPC_prefix_plus_segment
    (p : ProgramArtifact) (before segment : List Instr)
    (hsplit : p.instructions = before ++ segment) :
    p.instructionPC before.length + StackPC.byteLength segment = p.code.size := by
  have hassembly : (assembleBytes p.instructions).length = p.code.size := by
    have h := congrArg ByteArray.size p.assembly_eq
    change (assembleBytes p.instructions).toArray.size = p.code.size at h
    simpa only [List.size_toArray] using h
  have htake : (before ++ segment).take before.length = before := by
    simp
  unfold ProgramArtifact.instructionPC
  rw [hsplit, htake, StackPC.byteLength_eq_assemble]
  rw [hsplit, assembleBytes_append] at hassembly
  simpa only [List.length_append] using hassembly

private theorem instructionPC_segment_byteLength
    (p : ProgramArtifact) (before segment after : List Instr)
    (hsplit : p.instructions = before ++ segment ++ after)
    (i : Nat) (hi : i ≤ segment.length) :
    p.instructionPC (before.length + i) =
      p.instructionPC before.length + StackPC.byteLength (segment.take i) := by
  have hzero := ArtifactSegment.instructionPC_segment p before segment after hsplit 0
    (by omega : 0 ≤ segment.length)
  have hzero' : p.instructionPC before.length = (assembleBytes before).length := by
    simpa using hzero
  have hi' := ArtifactSegment.instructionPC_segment p before segment after hsplit i hi
  rw [StackPC.byteLength_eq_assemble, hzero']
  exact hi'

private theorem packedSchedule_slice :
    (Artifact.submissionArtifact.instructions.drop 2455).take
        PackedScheduleTemplate.ascendingPackedTemplate.length =
      PackedScheduleTemplate.ascendingPackedTemplate := by
  rfl

def packedScheduleSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      PackedScheduleTemplate.ascendingPackedTemplate :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    PackedScheduleTemplate.ascendingPackedTemplate 2455
    packedSchedule_slice
    (by
      change 2455 + PackedScheduleTemplate.ascendingPackedTemplate.length ≤
        Artifact.submissionInstructions.length
      rw [PackedScheduleTemplate.ascendingPackedTemplate_length,
        Artifact.referenceInstructions_count]
      decide)
    StackRoundData.artifact_code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := PackedScheduleTemplate.ascendingPackedTemplate) (by decide))
    (by decide)

private theorem packedScheduleFull_byteLength :
    StackPC.byteLength PackedScheduleTemplate.ascendingPackedFullTemplate = 528 := by
  rw [StackPC.byteLength_eq_assemble]
  exact PackedScheduleTemplate.ascendingPackedFullTemplate_byteLength

private theorem packedScheduleTemplate_byteLength :
    StackPC.byteLength PackedScheduleTemplate.ascendingPackedTemplate = 527 := by
  rw [StackPC.byteLength_eq_assemble]
  exact PackedScheduleTemplate.ascendingPackedTemplate_byteLength

private theorem packedSchedule_start_instructionPC :
    Artifact.submissionArtifact.instructionPC 2455 = 0x122c := by
  have h := instructionPC_prefix_plus_segment Artifact.submissionArtifact
    packedScheduleBefore PackedScheduleTemplate.ascendingPackedFullTemplate
    artifact_packed_split
  rw [packedScheduleBefore_length, packedScheduleFull_byteLength] at h
  have hsize : Artifact.submissionArtifact.code.size = 5180 := by
    change Challenge.Ripemd160.submissionBytecode.size = 5180
    exact Challenge.Ripemd160.referenceBytecode_size
  rw [hsize] at h
  omega

private theorem packedSchedule_end_instructionPC :
    Artifact.submissionArtifact.instructionPC 2614 = 0x143b := by
  have h := instructionPC_segment_byteLength Artifact.submissionArtifact
    packedScheduleBefore PackedScheduleTemplate.ascendingPackedTemplate
    PackedScheduleTemplate.finalJumpTemplate artifact_packed_split_prejump 159
    (by decide)
  have htake :
      PackedScheduleTemplate.ascendingPackedTemplate.take 159 =
        PackedScheduleTemplate.ascendingPackedTemplate := by
    apply List.take_of_length_le
    rw [PackedScheduleTemplate.ascendingPackedTemplate_length]
  rw [packedScheduleBefore_length, htake, packedScheduleTemplate_byteLength,
    packedSchedule_start_instructionPC] at h
  norm_num at h
  exact h

@[simp] theorem packedScheduleSite_startPC :
    packedScheduleSite.startPC = UInt256.ofNat 0x122c := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2455) =
    UInt256.ofNat 0x122c
  rw [packedSchedule_start_instructionPC]

@[simp] theorem packedScheduleSite_endPC :
    packedScheduleSite.endPC = UInt256.ofNat 0x143b := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2614) =
    UInt256.ofNat 0x143b
  rw [packedSchedule_end_instructionPC]

theorem packedScheduleSite_end_eq_pcAfter :
    packedScheduleSite.endPC =
      StackRoundTrace.pcAfter packedScheduleSite.startPC
        PackedScheduleTemplate.ascendingPackedTemplate := by
  have h := StackRoundTrace.endPC_eq_pcAfter_sites packedScheduleSite.sites
    packedScheduleSite.startPC packedScheduleSite.endPC packedScheduleSite.head_eq
    packedScheduleSite.end_eq packedScheduleSite.contiguous
  rwa [packedScheduleSite.instruction_eq] at h

private theorem pc_toNat_instructionPC (index : Nat) :
    (UInt256.ofNat (Artifact.submissionArtifact.instructionPC index)).toNat =
      Artifact.submissionArtifact.instructionPC index := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hle := Artifact.submissionArtifact.instructionPC_le_code_size index
  have hcode := StackRoundData.artifact_code_bound
  omega

def packedScheduleFinalJump :
    LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := 2614
      instruction := .op .JUMP
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2614)
  pc_eq := pc_toNat_instructionPC 2614

def packedScheduleFinalJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [packedScheduleFinalJump.located]

private theorem runLocatedBlock_singleton
    {artifact : ProgramArtifact} {fork : Fork}
    (located : Challenge.EvmProof.Stepper.Located artifact fork) (s : State) :
    Challenge.EvmProof.Stepper.runLocatedBlock [located] s =
      Challenge.EvmProof.Stepper.runLocated located s := by
  cases h : Challenge.EvmProof.Stepper.runLocated located s with
  | none => simp [Challenge.EvmProof.Stepper.runLocatedBlock, h]
  | some t => simp [Challenge.EvmProof.Stepper.runLocatedBlock, h]

@[simp] theorem packedScheduleFinalJump_pc :
    packedScheduleFinalJump.pc = UInt256.ofNat 0x143b := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 2614) =
    UInt256.ofNat 0x143b
  rw [packedSchedule_end_instructionPC]

theorem packedScheduleFinalJump_site_end :
    packedScheduleFinalJump.pc = packedScheduleSite.endPC := by
  calc
    packedScheduleFinalJump.pc = UInt256.ofNat 0x143b := packedScheduleFinalJump_pc
    _ = packedScheduleSite.endPC := packedScheduleSite_endPC.symm

theorem packedScheduleFinalJump_pc_eq_expected
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256) :
    packedScheduleFinalJump.pc =
      (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).pc := by
  calc
    packedScheduleFinalJump.pc = packedScheduleSite.endPC :=
      packedScheduleFinalJump_site_end
    _ = StackRoundTrace.pcAfter packedScheduleSite.startPC
        PackedScheduleTemplate.ascendingPackedTemplate :=
      packedScheduleSite_end_eq_pcAfter
    _ = (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).pc := by rfl

theorem runPackedScheduleFinalJump
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1023)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code returnPC.toNat = true) :
    Stepper.runLocatedBlock packedScheduleFinalJumpPath
      (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest) =
      some (Schedule.scheduleReturned
        (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest) returnPC rest) := by
  have hvalid' :
      Decode.isValidJumpDest
        (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.code returnPC.toNat = true := by
    simpa using hvalid
  have h := SharedCallTrace.runLocated_jump packedScheduleFinalJump (by rfl)
    (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
      messageOffset returnPC rest) returnPC rest hstack hvalid'
  have hstate :
      { PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest with
        pc := packedScheduleFinalJump.pc
        stack := returnPC :: rest } =
        PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest := by
    rw [packedScheduleFinalJump_pc_eq_expected s messageOffset returnPC rest]
    rfl
  rw [hstate] at h
  have hsingleton :
      Stepper.runLocatedBlock packedScheduleFinalJumpPath
          (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) =
        Stepper.runLocated packedScheduleFinalJump.located
          (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) := by
    exact runLocatedBlock_singleton _ _
  have hblock :
      Stepper.runLocatedBlock packedScheduleFinalJumpPath
          (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) =
        some { PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest with
          pc := returnPC
          stack := rest } := by
    calc
      Stepper.runLocatedBlock packedScheduleFinalJumpPath
          (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) =
          Stepper.runLocated packedScheduleFinalJump.located
            (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
              messageOffset returnPC rest) := hsingleton
      _ = some { PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest with
          pc := returnPC
          stack := rest } := h
  exact hblock

def gasSteps_packedSchedule_of_raw
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hresult :
      StackRoundTrace.runInstrSeq PackedScheduleTemplate.ascendingPackedTemplate
        (PackedScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
          messageOffset returnPC rest) =
      some (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest)) :
    GasSteps
      (PackedScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
        messageOffset returnPC rest)
      (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest) := by
  apply PackedScheduleLift.gasSteps_of_raw packedScheduleSite
    (s := PackedScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
      messageOffset returnPC rest)
    (t := PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
      messageOffset returnPC rest)
  · simpa [PackedScheduleTemplate.scheduleEntry] using hcode
  · simpa [PackedScheduleTemplate.scheduleEntry, State.fork] using hfork
  · simpa [PackedScheduleTemplate.scheduleEntry] using hrun
  · simpa [PackedScheduleTemplate.scheduleEntry] using hnp
  · rfl
  · exact ascendingPackedTemplate_advances
  · exact hresult

def gasSteps_packedSchedule_finalJump
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hstack : rest.length < 1023)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code returnPC.toNat = true) :
    GasSteps
      (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest)
      (Schedule.scheduleReturned
        (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest) returnPC rest) := by
  have hqcode :
      (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).executionEnv.code =
        Artifact.submissionArtifact.code := by
    simpa using hcode
  have hqfork :
      (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).fork = .Osaka := by
    simpa [State.fork] using hfork
  have hqrun :
      (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).halt = .Running := by
    simpa using hrun
  have hqnp :
      Precompile.isPrecompileWithConfig
        (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.precompileConfig
        (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.fork
        (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.codeAddr = false := by
    simpa using hnp
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    packedScheduleFinalJumpPath
  · exact hqcode
  · exact hqfork
  · exact runPackedScheduleFinalJump s messageOffset returnPC rest hstack hvalid
  · exact hqrun
  · exact hqnp

def gasSteps_packedSchedule
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hstack : rest.length < 1023)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code returnPC.toNat = true)
    (hresult :
      StackRoundTrace.runInstrSeq PackedScheduleTemplate.ascendingPackedTemplate
        (PackedScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
          messageOffset returnPC rest) =
      some (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
        messageOffset returnPC rest)) :
    GasSteps
      (PackedScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
        messageOffset returnPC rest)
      (Schedule.scheduleReturned
        (PackedScheduleTemplate.expectedState s packedScheduleSite.startPC
          messageOffset returnPC rest) returnPC rest) := by
  exact (gasSteps_packedSchedule_of_raw s messageOffset returnPC rest hcode hfork hrun hnp
    hresult).trans
    (gasSteps_packedSchedule_finalJump s messageOffset returnPC rest hcode hfork hrun hnp
      hstack hvalid)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite
