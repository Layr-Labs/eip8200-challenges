import Challenge.Ripemd160.Submission.Proofs.Bytecode.MemoryPackedOutput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80SiteCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLift
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.EvmProof.Word StackRoundTrace
@[simp] private theorem rawZeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
def packedHash (h : Compression.HashState) : UInt256 := (UInt256.lor (ofUInt32 h.h4) (UInt256.shiftLeft (UInt256.lor (ofUInt32 h.h3) (UInt256.shiftLeft (UInt256.lor (ofUInt32 h.h2) (UInt256.shiftLeft (UInt256.lor (ofUInt32 h.h1) (UInt256.shiftLeft (ofUInt32 h.h0) (UInt256.ofNat 32))) (UInt256.ofNat 32))) (UInt256.ofNat 32))) (UInt256.ofNat 32)))
def stored (s : State) (address : Nat) (word : UInt32) : State :=
  {s with memory := MemoryPackedOutput.store s.memory address word
          activeWords := s.activeWordsAfterUInt256 address 32}

def prepared (s : State) (h : Compression.HashState) : State :=
  let t := stored (stored (stored (stored (stored s 16 h.h4) 12 h.h3) 8 h.h2) 4 h.h1) 0 h.h0
  {t with activeWords := t.activeWordsAfterUInt256 16 32}

def entryTemplate : List Instr := [.op .JUMPDEST]
theorem entry_slice :
    (Artifact.submissionArtifact.instructions.drop 3484).take entryTemplate.length = entryTemplate := by rfl
def entrySite : StackRoundTemplate.GenericRoundSite Artifact.submissionArtifact .Osaka entryTemplate :=
  StackSiteBuilder.ofSlice entryTemplate 3484 entry_slice
    (by change 3484 + entryTemplate.length ≤ Artifact.submissionInstructions.length
        rw [Artifact.referenceInstructions_count]; decide)
    (by change submissionBytecode.size < 2^256; rw [referenceBytecode_size]; decide)
    (StackRoundData.templateWellFormed_mem (instructions := entryTemplate) (by decide)) (by decide)
theorem entry_pc : entrySite.startPC = UInt256.ofNat 4733 := by
  change UInt256.ofNat (Artifact.submissionArtifact.instructionPC 3484) = UInt256.ofNat 4733
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

def gasSteps_entry (s : State) (rho : List UInt256) (hstack : rho.length < 1024)
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4733, stack := rho}
      {s with pc := UInt256.ofNat 4734, stack := rho} := by
  apply PadLift.gasSteps_of_raw entrySite {s with pc := UInt256.ofNat 4733, stack := rho} _
    hcode hfork hrun hnp entry_pc.symm
  · apply PadLift.advancesAll_sound
    decide
  · simp [entryTemplate, runInstrSeq, DataStepper.runInstr, hrun, hstack]
    rfl

#print axioms gasSteps_entry
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
