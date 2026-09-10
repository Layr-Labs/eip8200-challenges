import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DenseScheduleTemplate

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PostStoreMaskInit
open EvmSemantics EvmSemantics.EVM
open DenseScheduleTemplate

def cachePath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨219, .push 30 mask16, by rfl, ⟨by decide, by decide⟩⟩,
   ⟨220, .push 31 mask8, by rfl, ⟨by decide, by decide⟩⟩]

def cachedState (s : State) : State :=
  { s with pc := UInt256.ofNat 468, stack := [mask8, mask16] }

theorem run_cache (s : State)
    (hpc : s.pc = UInt256.ofNat 405) (hstack : s.stack = [])
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock cachePath s =
      some (cachedState s) := by
  have hp1 : Artifact.submissionArtifact.instructionPC 219 = 405 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hp2 : Artifact.submissionArtifact.instructionPC 220 = 436 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  simp [cachePath, cachedState, hpc, hstack, hrun, hp1, hp2,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    mask8, mask16, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_cache (s : State)
    (hpc : s.pc = UInt256.ofNat 405) (hstack : s.stack = [])
    (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s (cachedState s) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka cachePath
  · exact hcode
  · exact hfork
  · exact run_cache s hpc hstack hrun
  · exact hrun
  · exact hnp
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PostStoreMaskInit

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.PostStoreMaskInit.gasSteps_cache
