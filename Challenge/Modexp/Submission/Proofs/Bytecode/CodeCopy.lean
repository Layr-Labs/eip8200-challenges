import Challenge.EvmProof.Ops

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.CodeCopy
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- Exact CODECOPY execution, including memory expansion and dynamic gas. -/
def step {s : State} {dest src size : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .CODECOPY)
    (hstack : s.stack = dest :: src :: size :: rest)
    (hcap : s.stack.length + Operation.pushArity .CODECOPY ≤
      1024 + Operation.popArity .CODECOPY)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps s {s with
      stack := rest
      pc := s.pc.succ
      activeWords := s.activeWordsAfterUInt256 dest.toNat size.toNat
      memory := MachineState.writeBytes s.memory
        (MachineState.readPadded s.executionEnv.code src.toNat size.toNat) dest.toNat} := by
  apply GasStep.of_running (Gas.codecopyTotal s dest size) hrun hnp
  intro gas hgas
  simpa [withGas, Gas.codecopyTotal, State.activeWordsAfterUInt256] using
    StepRunning.codecopy (withGas s gas) dest src size rest hop hstack hgas hcap

#print axioms step
end Challenge.Modexp.Submission.Proofs.Bytecode.CodeCopy
