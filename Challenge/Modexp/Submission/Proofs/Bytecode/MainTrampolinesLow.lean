import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactEarlyWordPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

theorem run_tramp0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState submissionBytecode input 0) = some (trampolineState input 0) := by
  -- Empty block: the relocated early-word block starts at pc 0, so the state
  -- the old trampoline produced is the state execution already begins in. The
  -- only residue is the pc field, literal `0` against `UInt256.ofNat 0`.
  simp [tramp0Path, Challenge.EvmProof.Stepper.runLocatedBlock, trampolineState,
    initialState, show (0 : UInt256) = UInt256.ofNat 0 from rfl]


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
