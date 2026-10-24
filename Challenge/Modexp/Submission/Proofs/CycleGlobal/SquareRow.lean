import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.SgtStep
import Challenge.Modexp.Submission.Proofs.Fast.SquareModel
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Mathlib.Algebra.Group.Fin.Basic

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
Environment and block-to-GasSteps adapters shared by the dedicated R4 square and
symbolic first-row arithmetic. The cached eight-limb square is proved in
`TnM128SquareFullSteps`; its prologue is in `TnM128SquareSteps`.
-/

namespace CycleSubmission.Global.Fast.SquareRow
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached SquareModel

def environment (s : State)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment CycleSubmission.Artifact.artifact .Osaka s :=
  ⟨by change CycleSubmission.Artifact.bytecode.size < 2^256
      rw [CycleSubmission.Artifact.bytecodeSize]; decide,
    hcode, hfork, hrun, hnp⟩

/-- `Block.steps` with the symbolic run first, so that the block's start state is read off
the run (used on record-update states). -/
def stepsOf {pc : Nat} {instructions : List Instr}
    (block : Block CycleSubmission.Artifact.artifact .Osaka pc instructions) {s t : State}
    (hrun' : runInstructions instructions s = some t) (hpc : s.pc = UInt256.ofNat pc)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  block.steps (environment s hcode hfork hrun hnp) hpc hrun'


end CycleSubmission.Global.Fast.SquareRow
