import Challenge.EvmProof.Ops
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SignedCompare
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
def step {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .SGT)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .SGT ≤
      1024 + Operation.popArity .SGT)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.sgt a b :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .SGT
  apply GasStep.of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.sgt (withGas s gas) a b rest hop hgas hstack hcap

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SignedCompare
