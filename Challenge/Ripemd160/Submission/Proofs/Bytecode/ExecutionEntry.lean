import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExecutionEntry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

deriving instance DecidableEq for Instr

def path : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  []

def entry (s : State) : State := { s with pc := UInt256.ofNat 0, stack := [] }
def finish (s : State) : State := { s with pc := UInt256.ofNat 0, stack := [] }

theorem run_entry (s : State)
    (_hcode : s.executionEnv.code = submissionBytecode) (_hrun : s.halt = .Running) :
    Stepper.runLocatedBlock path (entry s) = some (finish s) := by rfl

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
      { initialState submissionBytecode input 0 with pc := UInt256.ofNat 0 } :=
  generic (initialState submissionBytecode input 0) rfl rfl rfl deployAddress_not_precompile

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExecutionEntry
