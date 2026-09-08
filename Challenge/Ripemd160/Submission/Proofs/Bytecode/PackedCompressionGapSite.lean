import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedReadWindow

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-!
# Located per-block packed-gap initialization

The packed compression entry keeps its landing `JUMPDEST` at PC 538.  The
three instructions immediately after it clear a full word at address 272,
which establishes the eight-byte gap premise used by the final right-lane
read.  The rest of the packed compression trace starts at PC 544.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionGapSite

open Challenge.Ripemd160 Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

/-- Exact locations of `PUSH0; PUSH2 0x110; MSTORE`. -/
def gapPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨297, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨298, .push ⟨2, by decide⟩ (UInt256.ofNat 272), by rfl, by decide⟩,
   ⟨299, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Entry immediately after the compression landing `JUMPDEST`. -/
def gapEntry (s : State) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 539, stack := rest }

/-- State after the explicit zero store and before packed preprocessing. -/
def gapCleared (s : State) (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 544
    stack := rest
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded 0 32) 272
    activeWords := s.activeWordsAfterUInt256 272 32 }

@[simp] theorem gapCleared_memory (s : State) (rest : List UInt256) :
    (gapCleared s rest).memory = MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded 0 32) 272 := by
  rfl

@[simp] theorem gapCleared_stack (s : State) (rest : List UInt256) :
    (gapCleared s rest).stack = rest := by
  rfl

@[simp] theorem gapCleared_pc (s : State) (rest : List UInt256) :
    (gapCleared s rest).pc = UInt256.ofNat 544 := by
  rfl

theorem gapCleared_gapZero (s : State) (rest : List UInt256) :
    PackedGapInvariant.GapZero (gapCleared s rest).memory := by
  exact PackedReadWindow.clear_gap_store s.memory

set_option linter.unusedSimpArgs false in
theorem run_gapPath (s : State) (rest : List UInt256)
    (hstack : rest.length + 2 < 1024) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock gapPath (gapEntry s rest) =
      some (gapCleared s rest) := by
  have hpc297 : Artifact.submissionArtifact.instructionPC 297 = 539 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hpc298 : Artifact.submissionArtifact.instructionPC 298 = 540 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hpc299 : Artifact.submissionArtifact.instructionPC 299 = 543 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  simp [gapPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    gapEntry, gapCleared, hpc297, hpc298, hpc299, hc0, hc1, hstack, hrun,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]
  constructor <;> rfl

/-- The executable three-instruction trace, ready to prepend to the packed
preprocessing certificate. -/
def gasSteps_gapPath (s : State) (rest : List UInt256)
    (hstack : rest.length + 2 < 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (gapEntry s rest) (gapCleared s rest) := by
  have hartifactCode :
      s.executionEnv.code = Artifact.submissionArtifact.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  apply Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka gapPath
  · simpa [gapEntry] using hartifactCode
  · simpa [gapEntry] using hfork
  · exact run_gapPath s rest hstack hrun
  · simpa [gapEntry] using hrun
  · simpa [gapEntry] using hnp

#print axioms gapCleared_gapZero
#print axioms gasSteps_gapPath

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionGapSite
