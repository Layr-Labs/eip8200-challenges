import Challenge.EvmProof.Ops

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Codesize

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

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

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Codesize
