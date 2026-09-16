import Challenge.Modexp.Submission.Proofs.Fast.SgtStep
import Challenge.Modexp.Submission.Proofs.Fast.SquareModel
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Mathlib.Algebra.Group.Fin.Basic

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
Environment and block-to-GasSteps adapters shared by the dedicated R4 square and
symbolic first-row arithmetic. The cached eight-limb square is proved in
`TnM128SquareFullSteps`; its prologue is in `TnM128SquareSteps`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRow

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256
      rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

/-- `Block.steps` with the symbolic run first, so that the block's start state is read off
the run (used on record-update states). -/
def stepsOf {pc : Nat} {instructions : List Instr}
    (block : Block Artifact.submissionArtifact .Osaka pc instructions) {s t : State}
    (hrun' : runInstructions instructions s = some t) (hpc : s.pc = UInt256.ofNat pc)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  block.steps (environment s hcode hfork hrun hnp) hpc hrun'


end Challenge.Modexp.Submission.Proofs.Fast.SquareRow
