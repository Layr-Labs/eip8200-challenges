import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianMultiply
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleLift
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.QuadLayout
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRoundData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackSiteBuilder
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength

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

private theorem initialTemplate_advances :
    ∀ instruction ∈ DenseScheduleTemplate.initialTemplate,
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [DenseScheduleTemplate.initialTemplate, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact advances_jumpdest
  all_goals exact advances_straight (by constructor)

private theorem denseStore_advances (half : Nat) :
    ∀ instruction ∈
      [DenseScheduleTemplate.push1
          (UInt256.ofNat (DenseScheduleTemplate.denseStoreAddress half)),
        DenseScheduleTemplate.op .MSTORE],
      DenseScheduleLift.Advances instruction := by
  intro instruction hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact advances_straight (by constructor)
  · exact advances_mstore

private theorem denseHalfTemplate_runInstr_pc (half : Nat) :
    ∀ instruction ∈ DenseScheduleTemplate.denseHalfTemplate half,
      ∀ {s t : State}, Stepper.runInstr instruction s = some t →
        t.pc = s.pc + UInt256.ofNat instruction.size := by
  intro instruction hmem s t hresult
  simp only [DenseScheduleTemplate.denseHalfTemplate, List.mem_append] at hmem
  rcases hmem with (h8 | h16) | hstore
  · apply ClosedEndianMultiply.advances 8 ?_ hresult
    simpa [ClosedEndianMultiply.code, DenseScheduleTemplate.endianStage8,
      DenseScheduleTemplate.endianStage, DenseScheduleTemplate.endianMaskTemplate]
      using h8
  · apply ClosedEndianMultiply.advances 16 ?_ hresult
    simpa [ClosedEndianMultiply.code, DenseScheduleTemplate.endianStage16,
      DenseScheduleTemplate.endianStage, DenseScheduleTemplate.endianMaskTemplate]
      using h16
  · exact DenseScheduleLift.runInstr_pc_of_advances
      (denseStore_advances half instruction hstore) hresult

private theorem denseBeforeJumpTemplate_runInstr_pc :
    ∀ instruction ∈ DenseScheduleTemplate.denseBeforeJumpTemplate,
      ∀ {s t : State}, Stepper.runInstr instruction s = some t →
        t.pc = s.pc + UInt256.ofNat instruction.size := by
  intro instruction hmem s t hresult
  simp only [DenseScheduleTemplate.denseBeforeJumpTemplate, List.mem_append] at hmem
  rcases hmem with (hinitial | h1) | h0
  · exact DenseScheduleLift.runInstr_pc_of_advances
      (initialTemplate_advances instruction hinitial) hresult
  · exact denseHalfTemplate_runInstr_pc 1 instruction h1 hresult
  · exact denseHalfTemplate_runInstr_pc 0 instruction h0 hresult

private theorem packedSchedule_slice :
    (Artifact.submissionArtifact.instructions.drop 288).take
        DenseScheduleTemplate.denseBeforeJumpTemplate.length =
      DenseScheduleTemplate.denseBeforeJumpTemplate := by
  rfl

def packedScheduleSite :
    GenericRoundSite Artifact.submissionArtifact .Osaka
      DenseScheduleTemplate.denseBeforeJumpTemplate :=
  StackSiteBuilder.ofSlice
    (artifact := Artifact.submissionArtifact) (fork := .Osaka)
    DenseScheduleTemplate.denseBeforeJumpTemplate 288
    packedSchedule_slice
    (by
      change 288 + DenseScheduleTemplate.denseBeforeJumpTemplate.length ≤
        Artifact.submissionInstructions.length
      rw [DenseScheduleTemplate.denseBeforeJumpTemplate_length,
        Artifact.referenceInstructions_count]
      decide)
    QuadLayout.code_bound
    (StackRoundData.templateWellFormed_mem
      (instructions := DenseScheduleTemplate.denseBeforeJumpTemplate) (by decide))
    (by decide)

private theorem denseScheduleTemplate_byteLength :
    byteLength DenseScheduleTemplate.denseBeforeJumpTemplate = 90 := by
  rw [byteLength_eq_assemble]
  exact DenseScheduleTemplate.denseBeforeJumpTemplate_byteLength

private theorem packedSchedule_start_instructionPC :
    Artifact.submissionArtifact.instructionPC 288 = 0x208 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

private theorem packedSchedule_end_instructionPC :
    Artifact.submissionArtifact.instructionPC 351 = 0x262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  rfl

@[simp] theorem packedScheduleSite_startPC :
    packedScheduleSite.startPC = UInt256.ofNat 0x208 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 288) =
    UInt256.ofNat 0x208
  rw [packedSchedule_start_instructionPC]

@[simp] theorem packedScheduleSite_endPC :
    packedScheduleSite.endPC = UInt256.ofNat 0x262 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 351) =
    UInt256.ofNat 0x262
  rw [packedSchedule_end_instructionPC]

theorem packedScheduleSite_end_eq_pcAfter :
    packedScheduleSite.endPC =
      StackRoundTrace.pcAfter packedScheduleSite.startPC
        DenseScheduleTemplate.denseBeforeJumpTemplate := by
  have h := StackRoundTrace.endPC_eq_pcAfter_sites packedScheduleSite.sites
    packedScheduleSite.startPC packedScheduleSite.endPC packedScheduleSite.head_eq
    packedScheduleSite.end_eq packedScheduleSite.contiguous
  rwa [packedScheduleSite.instruction_eq] at h

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
  let entry := DenseScheduleTemplate.scheduleEntry s packedScheduleSite.startPC
    messageOffset returnPC rest
  have hlocated : Stepper.runLocatedBlock packedScheduleSite.path entry =
      some (DenseScheduleTemplate.denseExpectedState s packedScheduleSite.startPC
        messageOffset returnPC rest) := by
    rw [StackRoundTrace.runLocatedBlock_eq_runInstrSeq_site packedScheduleSite
      entry rfl (by
        intro located hmem u v hinstr
        apply denseBeforeJumpTemplate_runInstr_pc located.located.instruction ?_ hinstr
        rw [← packedScheduleSite.instruction_eq]
        exact List.mem_map_of_mem hmem)]
    exact hresult
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    packedScheduleSite.path
  · simpa [entry, DenseScheduleTemplate.scheduleEntry] using hcode
  · simpa [entry, DenseScheduleTemplate.scheduleEntry, State.fork] using hfork
  · exact hlocated
  · simpa [entry, DenseScheduleTemplate.scheduleEntry] using hrun
  · simpa [entry, DenseScheduleTemplate.scheduleEntry] using hnp


end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedScheduleSite
