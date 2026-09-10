import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExecutionEntry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

deriving instance DecidableEq for Instr

def initial_entry (input : ByteArray) :
    GasSteps (initialState submissionBytecode input 0)
      { initialState submissionBytecode input 0 with pc := UInt256.ofNat 0 } := by
  exact GasSteps.refl _

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExecutionEntry
