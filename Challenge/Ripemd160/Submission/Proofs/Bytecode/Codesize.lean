import Challenge.EvmProof.Ops

set_option warningAsError true

/-! A gas-accounted rule for `CODESIZE`.  The generic straight-line evaluator
does not expose this opcode, so the submission proves the corresponding EVM
step directly through the shared gas-step interface. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Codesize

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof

def step {s : State}
    (hop : s.decodedOp = some .CODESIZE)
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := UInt256.ofNat s.executionEnv.code.size :: s.stack,
      pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .CODESIZE
  apply GasStep.of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.codesize (withGas s gas) hop hgas hcap

@[simp] theorem step_cost {s : State}
    (hop : s.decodedOp = some .CODESIZE)
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    (step hop hcap hrun hnp).cost = 2 := rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Codesize
