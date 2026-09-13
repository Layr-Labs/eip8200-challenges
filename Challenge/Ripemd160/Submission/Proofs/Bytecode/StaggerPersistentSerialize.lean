import Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndianRescheduled
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FundedOutputEndian
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianLiteralBounds
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerialize
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def endian8Code : List Instr := FundedOutputEndian.code8
theorem endian8_slice : (Artifact.submissionArtifact.instructions.drop 3656).take endian8Code.length = endian8Code := by rfl
def endian8Site : GenericRoundSite Artifact.submissionArtifact .Osaka endian8Code :=
  StackSiteBuilder.ofSlice endian8Code 3656 endian8_slice
    (by change 3656 + endian8Code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := endian8Code) (by decide)) (by decide)
theorem endian8_pc : endian8Site.startPC = UInt256.ofNat 4666 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3656) = UInt256.ofNat 4666
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem endian8_end : endian8Site.endPC = UInt256.ofNat 4679 := by
  have h := endPC_eq_pcAfter_sites endian8Site.sites endian8Site.startPC endian8Site.endPC
    endian8Site.head_eq endian8Site.end_eq endian8Site.contiguous
  rw [endian8Site.instruction_eq, endian8_pc] at h
  exact h.trans (by decide)

def endian16Code : List Instr := FundedOutputEndianRescheduled.code
theorem endian16_slice : (Artifact.submissionArtifact.instructions.drop 3666).take endian16Code.length = endian16Code := by rfl
def endian16Site : GenericRoundSite Artifact.submissionArtifact .Osaka endian16Code :=
  StackSiteBuilder.ofSlice endian16Code 3666 endian16_slice
    (by change 3666 + endian16Code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := endian16Code) (by decide)) (by decide)
theorem endian16_pc : endian16Site.startPC = UInt256.ofNat 4679 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3666) = UInt256.ofNat 4679
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem endian16_end : endian16Site.endPC = UInt256.ofNat 4693 := by
  have h := endPC_eq_pcAfter_sites endian16Site.sites endian16Site.startPC endian16Site.endPC
    endian16Site.head_eq endian16Site.end_eq endian16Site.contiguous
  rw [endian16Site.instruction_eq, endian16_pc] at h
  exact h.trans (by decide)

def terminalCode : List Instr := StaggerPersistentReturn.template
theorem terminal_slice : (Artifact.submissionArtifact.instructions.drop 3676).take terminalCode.length = terminalCode := by rfl
def terminalSite : GenericRoundSite Artifact.submissionArtifact .Osaka terminalCode :=
  StackSiteBuilder.ofSlice terminalCode 3676 terminal_slice
    (by change 3676 + terminalCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := terminalCode) (by decide)) (by decide)
theorem terminal_pc : terminalSite.startPC = UInt256.ofNat 4693 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3676) = UInt256.ofNat 4693
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def value (h : Compression.HashState) : UInt256 :=
  DenseScheduleTemplate.packedWord (StaggerPersistentOutput.packedHash h)
def result (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : State :=
  StaggerPersistentReturn.result s (UInt256.ofNat 4693) (value h) (off :: limit :: rho)

def gasSteps (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4643, stack := StaggerPersistentFrame.frame h off limit (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)}
      (result s h off limit (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)) := by
  have gp := StaggerPersistentOutput.gasSteps s off limit h
    (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho) (by simp; omega) hrun hcode hfork hnp
  have g8 := FundedOutputEndian.gasSteps8 endian8Site
    s (StaggerPersistentOutput.packedHash h) off limit (DenseScheduleTemplate.mask16 :: rho)
    (by simp; omega) hcode hfork hrun hnp
  have g16 := FundedOutputEndianRescheduled.gasSteps_endian endian16Site
    s (DenseScheduleTemplate.packedStage (StaggerPersistentOutput.packedHash h) 8 DenseScheduleTemplate.mask8)
    off limit DenseScheduleTemplate.mask8 rho (by omega) hcode hfork hrun hnp
  have gt := StaggerPersistentReturn.gasSteps_site terminalSite s (value h)
    (off :: limit :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)
    (by simp; omega) hcode hfork hrun hnp
  rw [endian8_pc,endian8_end] at g8
  rw [endian16_pc,endian16_end] at g16
  rw [terminal_pc] at gt
  exact gp.trans (g8.trans (g16.trans gt))
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerialize
