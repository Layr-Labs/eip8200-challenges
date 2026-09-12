import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianReuse
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerialize
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def entryCode : List Instr := [.op .JUMPDEST]
theorem entry_slice : (Artifact.submissionArtifact.instructions.drop 3806).take entryCode.length = entryCode := by rfl
def entrySite : GenericRoundSite Artifact.submissionArtifact .Osaka entryCode :=
  StackSiteBuilder.ofSlice entryCode 3806 entry_slice
    (by change 3806 + entryCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := entryCode) (by decide)) (by decide)
theorem entry_pc : entrySite.startPC = UInt256.ofNat 4748 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3806) = UInt256.ofNat 4748
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem entry_end : entrySite.endPC = UInt256.ofNat 4749 := by
  have h := endPC_eq_pcAfter_sites entrySite.sites entrySite.startPC entrySite.endPC
    entrySite.head_eq entrySite.end_eq entrySite.contiguous
  rw [entrySite.instruction_eq, entry_pc] at h
  exact h.trans (by decide)

def endian8Code : List Instr := ClosedEndianReuse.code 8
theorem endian8_slice : (Artifact.submissionArtifact.instructions.drop 3819).take endian8Code.length = endian8Code := by rfl
def endian8Site : GenericRoundSite Artifact.submissionArtifact .Osaka endian8Code :=
  StackSiteBuilder.ofSlice endian8Code 3819 endian8_slice
    (by change 3819 + endian8Code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := endian8Code) (by decide)) (by decide)
theorem endian8_pc : endian8Site.startPC = UInt256.ofNat 4765 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3819) = UInt256.ofNat 4765
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem endian8_end : endian8Site.endPC = UInt256.ofNat 4781 := by
  have h := endPC_eq_pcAfter_sites endian8Site.sites endian8Site.startPC endian8Site.endPC
    endian8Site.head_eq endian8Site.end_eq endian8Site.contiguous
  rw [endian8Site.instruction_eq, endian8_pc] at h
  exact h.trans (by decide)

def endian16Code : List Instr := ClosedEndianReuse.code 16
theorem endian16_slice : (Artifact.submissionArtifact.instructions.drop 3832).take endian16Code.length = endian16Code := by rfl
def endian16Site : GenericRoundSite Artifact.submissionArtifact .Osaka endian16Code :=
  StackSiteBuilder.ofSlice endian16Code 3832 endian16_slice
    (by change 3832 + endian16Code.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := endian16Code) (by decide)) (by decide)
theorem endian16_pc : endian16Site.startPC = UInt256.ofNat 4781 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3832) = UInt256.ofNat 4781
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
theorem endian16_end : endian16Site.endPC = UInt256.ofNat 4798 := by
  have h := endPC_eq_pcAfter_sites endian16Site.sites endian16Site.startPC endian16Site.endPC
    endian16Site.head_eq endian16Site.end_eq endian16Site.contiguous
  rw [endian16Site.instruction_eq, endian16_pc] at h
  exact h.trans (by decide)

def terminalCode : List Instr := StaggerPersistentReturn.template
theorem terminal_slice : (Artifact.submissionArtifact.instructions.drop 3845).take terminalCode.length = terminalCode := by rfl
def terminalSite : GenericRoundSite Artifact.submissionArtifact .Osaka terminalCode :=
  StackSiteBuilder.ofSlice terminalCode 3845 terminal_slice
    (by change 3845 + terminalCode.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := terminalCode) (by decide)) (by decide)
theorem terminal_pc : terminalSite.startPC = UInt256.ofNat 4798 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3845) = UInt256.ofNat 4798
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def value (h : Compression.HashState) : UInt256 :=
  DenseScheduleTemplate.packedWord (StaggerPersistentOutput.packedHash h)
def result (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : State :=
  StaggerPersistentReturn.result s (UInt256.ofNat 4798) (value h) (off :: limit :: rho)

def gasSteps_entry (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4748, stack := rho}
      {s with pc := UInt256.ofNat 4749, stack := rho} := by
  apply DenseScheduleLift.gasSteps_of_raw entrySite
    {s with pc := UInt256.ofNat 4748, stack := rho}
    {s with pc := UInt256.ofNat 4749, stack := rho}
    hcode hfork hrun hnp entry_pc.symm
    (Table80SiteCommon.coreAdvancesAll_sound entryCode (by decide))
  simp [entryCode, runInstrSeq, Stepper.runInstr, hrun, hstack, UInt256.succ]
  all_goals rfl

def gasSteps (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4748, stack := StaggerPersistentFrame.frame h off limit rho}
      (result s h off limit rho) := by
  have ge := gasSteps_entry s (StaggerPersistentFrame.frame h off limit rho)
    (by simp [StaggerPersistentFrame.frame]; omega) hcode hfork hrun hnp
  have gp := StaggerPersistentOutput.gasSteps s off limit h rho (by omega) hrun hcode hfork hnp
  have g8 := ClosedEndianReuse.gasSteps_endian 8 DenseScheduleTemplate.mask8 endian8Site
    s (StaggerPersistentOutput.packedHash h) (off::limit::rho) (by simp; omega) (Or.inl ⟨rfl,rfl⟩) hcode hfork hrun hnp
  have g16 := ClosedEndianReuse.gasSteps_endian 16 DenseScheduleTemplate.mask16 endian16Site
    s (DenseScheduleTemplate.packedStage (StaggerPersistentOutput.packedHash h) 8 DenseScheduleTemplate.mask8)
    (off::limit::rho) (by simp; omega) (Or.inr ⟨rfl,rfl⟩) hcode hfork hrun hnp
  have gt := StaggerPersistentReturn.gasSteps_site terminalSite s (value h) (off::limit::rho)
    (by simp; omega) hcode hfork hrun hnp
  rw [endian8_pc,endian8_end] at g8
  rw [endian16_pc,endian16_end] at g16
  rw [terminal_pc] at gt
  exact ge.trans (gp.trans (g8.trans (g16.trans gt)))
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerialize
