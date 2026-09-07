import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
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

private def byteLength : List Instr → Nat
  | [] => 0
  | .op _ :: rest => 1 + byteLength rest
  | .push width _ :: rest => (1 + width.val) + byteLength rest

private theorem byteLength_eq_assemble (instructions : List Instr) :
    byteLength instructions = (assembleBytes instructions).length := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
    cases instruction <;> simp [byteLength, assembleBytes_cons, ih, Nat.add_comm]


private theorem advances_straight {instruction : Instr}
    (h : StraightLine instruction) : DenseScheduleLift.Advances instruction := by
  exact Or.inl (Or.inl h)

private theorem advances_jumpdest :
    DenseScheduleLift.Advances (.op .JUMPDEST) := by
  exact Or.inl (Or.inr (Or.inr rfl))

private theorem advances_mstore :
    DenseScheduleLift.Advances (.op .MSTORE) := by
  exact Or.inr (Or.inl rfl)

private theorem advances_mul :
    DenseScheduleLift.Advances (.op .MUL) := by
  exact Or.inr (Or.inr rfl)

private theorem initialTemplate_advances :
    ∀ instruction ∈ DenseScheduleTemplate.initialTemplate,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [DenseScheduleTemplate.initialTemplate, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact advances_jumpdest
  all_goals exact advances_straight (by constructor)

private theorem endianStage_advances (shift : Nat) (mask : UInt256) :
    ∀ instruction ∈ DenseScheduleTemplate.endianStage shift mask,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [DenseScheduleTemplate.endianStage, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact advances_mul
    | exact advances_straight (by constructor)
    | apply advances_straight
      unfold DenseScheduleTemplate.endianFactorPush
      split <;> constructor
    | apply advances_straight
      unfold DenseScheduleTemplate.endianMaskPush
      split <;> constructor

private theorem denseStore_advances (half : Nat) :
    ∀ instruction ∈
      [DenseScheduleTemplate.push2
          (UInt256.ofNat (DenseScheduleTemplate.denseStoreAddress half)),
        DenseScheduleTemplate.op .MSTORE],
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact advances_straight (by constructor)
  · exact advances_mstore

private theorem denseHalfTemplate_advances (half : Nat) :
    ∀ instruction ∈ DenseScheduleTemplate.denseHalfTemplate half,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [DenseScheduleTemplate.denseHalfTemplate, List.mem_append] at hmem
  rcases hmem with (h8 | h16) | hstore
  · exact endianStage_advances 8 DenseScheduleTemplate.mask8 instruction h8
  · exact endianStage_advances 16 DenseScheduleTemplate.mask16 instruction h16
  · exact denseStore_advances half instruction hstore

private theorem denseBeforeJumpTemplate_advances :
    ∀ instruction ∈ DenseScheduleTemplate.denseBeforeJumpTemplate,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [DenseScheduleTemplate.denseBeforeJumpTemplate, List.mem_append] at hmem
  rcases hmem with (hinitial | h1) | h0
  · exact initialTemplate_advances instruction hinitial
  · exact denseHalfTemplate_advances 1 instruction h1
  · exact denseHalfTemplate_advances 0 instruction h0

private theorem packedSchedule_slice :
    (Artifact.submissionArtifact.instructions.drop 3249).take
        DenseScheduleTemplate.denseBeforeJumpTemplate.length =
      DenseScheduleTemplate.denseBeforeJumpTemplate := by
  rfl

def packedScheduleSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      DenseScheduleTemplate.denseBeforeJumpTemplate :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    DenseScheduleTemplate.denseBeforeJumpTemplate 3249
    packedSchedule_slice
    (by
      change 3249 + DenseScheduleTemplate.denseBeforeJumpTemplate.length ≤
        Artifact.submissionInstructions.length
      rw [DenseScheduleTemplate.denseBeforeJumpTemplate_length,
        Artifact.referenceInstructions_count]
      decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := DenseScheduleTemplate.denseBeforeJumpTemplate) (by decide))
    (by decide)

private theorem denseScheduleTemplate_byteLength :
    byteLength DenseScheduleTemplate.denseBeforeJumpTemplate = 192 := by
  rw [byteLength_eq_assemble]
  exact DenseScheduleTemplate.denseBeforeJumpTemplate_byteLength

private theorem packedSchedule_start_instructionPC :
    Artifact.submissionArtifact.instructionPC 3249 = 0x1267 :=
  QuadLayout.schedule_pc

private theorem packedSchedule_end_instructionPC :
    Artifact.submissionArtifact.instructionPC 3300 = 0x1327 :=
  QuadLayout.scheduleJump_pc

@[simp] theorem packedScheduleSite_startPC :
    packedScheduleSite.startPC = UInt256.ofNat 0x1267 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3249) =
    UInt256.ofNat 0x1267
  rw [packedSchedule_start_instructionPC]

@[simp] theorem packedScheduleSite_endPC :
    packedScheduleSite.endPC = UInt256.ofNat 0x1327 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3300) =
    UInt256.ofNat 0x1327
  rw [packedSchedule_end_instructionPC]

theorem packedScheduleSite_end_eq_pcAfter :
    packedScheduleSite.endPC =
      StackRoundTrace.pcAfter packedScheduleSite.startPC
        DenseScheduleTemplate.denseBeforeJumpTemplate := by
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
  have hcode := QuadLayout.code_bound
  exact Nat.lt_of_le_of_lt hle hcode

def packedScheduleFinalJump :
    LocatedSite Artifact.submissionArtifact .Osaka where
  located :=
    { index := 3300
      instruction := .op .JUMP
      atIndex := by rfl
      wellFormed := ⟨by decide, trivial, rfl⟩ }
  pc := UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3300)
  pc_eq := pc_toNat_instructionPC 3300

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
    packedScheduleFinalJump.pc = UInt256.ofNat 0x1327 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3300) =
    UInt256.ofNat 0x1327
  rw [packedSchedule_end_instructionPC]

theorem packedScheduleFinalJump_site_end :
    packedScheduleFinalJump.pc = packedScheduleSite.endPC := by
  calc
    packedScheduleFinalJump.pc = UInt256.ofNat 0x1327 := packedScheduleFinalJump_pc
    _ = packedScheduleSite.endPC := packedScheduleSite_endPC.symm

theorem packedScheduleFinalJump_pc_eq_expected
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256) :
    packedScheduleFinalJump.pc =
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).pc := by
  calc
    packedScheduleFinalJump.pc = packedScheduleSite.endPC :=
      packedScheduleFinalJump_site_end
    _ = StackRoundTrace.pcAfter packedScheduleSite.startPC
        DenseScheduleTemplate.denseBeforeJumpTemplate :=
      packedScheduleSite_end_eq_pcAfter
    _ = (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).pc := by rfl

theorem runPackedScheduleFinalJump
    (s : State) (messageOffset returnPC : UInt256) (rest : List UInt256)
    (hstack : rest.length < 1023)
    (hvalid : Decode.isValidJumpDest s.executionEnv.code returnPC.toNat = true) :
    Stepper.runLocatedBlock packedScheduleFinalJumpPath
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest) =
      some (Schedule.scheduleReturned
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest) returnPC rest) := by
  have hvalid' :
      Decode.isValidJumpDest
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.code returnPC.toNat = true := by
    simpa [DenseScheduleTemplate.denseExpectedState] using hvalid
  have h := SharedCallTrace.runLocated_jump packedScheduleFinalJump (by rfl)
    (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
      messageOffset returnPC rest) returnPC rest hstack hvalid'
  have hstate :
      { DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest with
        pc := packedScheduleFinalJump.pc
        stack := returnPC :: rest } =
        DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest := by
    rw [packedScheduleFinalJump_pc_eq_expected s messageOffset returnPC rest]
    rfl
  rw [hstate] at h
  have hsingleton :
      Stepper.runLocatedBlock packedScheduleFinalJumpPath
          (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) =
        Stepper.runLocated packedScheduleFinalJump.located
          (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) := by
    exact runLocatedBlock_singleton _ _
  have hblock :
      Stepper.runLocatedBlock packedScheduleFinalJumpPath
          (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) =
        some { DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest with
          pc := returnPC
          stack := rest } := by
    calc
      Stepper.runLocatedBlock packedScheduleFinalJumpPath
          (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
            messageOffset returnPC rest) =
          Stepper.runLocated packedScheduleFinalJump.located
            (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
              messageOffset returnPC rest) := hsingleton
      _ = some { DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
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
      StackRoundTrace.runInstrSeq DenseScheduleTemplate.denseBeforeJumpTemplate
        (DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
          messageOffset returnPC rest) =
      some (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest)) :
    GasSteps
      (DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
        messageOffset returnPC rest)
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest) := by
  apply DenseScheduleLift.gasSteps_of_raw packedScheduleSite
    (s := DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
      messageOffset returnPC rest)
    (t := DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
      messageOffset returnPC rest)
  · simpa [DenseScheduleTemplate.scheduleEntry] using hcode
  · simpa [DenseScheduleTemplate.scheduleEntry, State.fork] using hfork
  · simpa [DenseScheduleTemplate.scheduleEntry] using hrun
  · simpa [DenseScheduleTemplate.scheduleEntry] using hnp
  · rfl
  · exact denseBeforeJumpTemplate_advances
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
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest)
      (Schedule.scheduleReturned
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest) returnPC rest) := by
  have hqcode :
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).executionEnv.code =
        Artifact.submissionArtifact.code := by
    simpa [DenseScheduleTemplate.denseExpectedState] using hcode
  have hqfork :
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).fork = .Osaka := by
    simpa [DenseScheduleTemplate.denseExpectedState, State.fork] using hfork
  have hqrun :
      (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest).halt = .Running := by
    simpa [DenseScheduleTemplate.denseExpectedState] using hrun
  have hqnp :
      Precompile.isPrecompileWithConfig
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.precompileConfig
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.fork
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest).executionEnv.codeAddr = false := by
    simpa [DenseScheduleTemplate.denseExpectedState] using hnp
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
      StackRoundTrace.runInstrSeq DenseScheduleTemplate.denseBeforeJumpTemplate
        (DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
          messageOffset returnPC rest) =
      some (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest)) :
    GasSteps
      (DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
        messageOffset returnPC rest)
      (Schedule.scheduleReturned
        (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
          messageOffset returnPC rest) returnPC rest) := by
  exact (gasSteps_packedSchedule_of_raw s messageOffset returnPC rest hcode hfork hrun hnp
    hresult).trans
    (gasSteps_packedSchedule_finalJump s messageOffset returnPC rest hcode hfork hrun hnp
      hstack hvalid)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite
