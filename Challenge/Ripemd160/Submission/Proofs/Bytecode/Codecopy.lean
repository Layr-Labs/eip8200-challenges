import Challenge.EvmProof.Ops
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Codecopy
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
/-- Gas-accounted own-code copy, derived directly from EVM semantics. -/
def step {s : State} (destOff srcOff sz : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .CODECOPY)
    (hstack : s.stack = destOff :: srcOff :: sz :: rest)
    (hcap : s.stack.length + Operation.pushArity .CODECOPY ≤ 1024 + Operation.popArity .CODECOPY)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s {s with
      stack := rest,
      pc := s.pc.succ,
      activeWords := s.activeWordsAfterUInt256 destOff.toNat sz.toNat,
      memory := MachineState.writeBytes s.memory
        (MachineState.readPadded s.executionEnv.code srcOff.toNat sz.toNat) destOff.toNat} := by
  let cost := Gas.codecopyTotal s destOff sz
  apply GasStep.of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, Gas.codecopyTotal, State.activeWordsAfterUInt256] using
    StepRunning.codecopy (withGas s gas) destOff srcOff sz rest hop hstack hgas hcap
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Codecopy
