import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExecutionEntry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

deriving instance DecidableEq for Instr

theorem destination : Decode.isValidJumpDest submissionBytecode 0xae = true := by
  have hget : Artifact.submissionArtifact.instructions[97]? = some (.op .JUMPDEST) := by
    decide
  have hpc : Artifact.submissionArtifact.instructionPC 101 = 0xae := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 101 hget
  rw [hpc] at h
  exact h

def path : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨0, .push ⟨1, by decide⟩ (UInt256.ofNat 174), by rfl, by decide⟩,
   ⟨1, .op .JUMP, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def entry (s : State) : State := { s with pc := UInt256.ofNat 0, stack := [] }
def finish (s : State) : State := { s with pc := UInt256.ofNat 0xae, stack := [] }

theorem run_entry (s : State)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock path (entry s) = some (finish s) := by
  have hdestNat : (UInt256.ofNat 0xae).toNat = 0xae := by decide
  simp [path, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    entry, finish, hcode, hrun, hdestNat, destination,
    Word.word_toNat_ofNat, Word.ofNat_add_mod]

def generic (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s) (finish s) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path
    hcode hfork (run_entry s hcode hrun) hrun hnp

def initial_entry (input : ByteArray) :
    GasSteps (initialState submissionBytecode input 0)
      { initialState submissionBytecode input 0 with pc := UInt256.ofNat 0xae } :=
  generic (initialState submissionBytecode input 0) rfl rfl rfl deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExecutionEntry
