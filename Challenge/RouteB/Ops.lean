import Challenge.RouteB.Gas
set_option warningAsError true
/-!
# Gas-parametric opcode transitions

Small wrappers around `EvmSemantics.EVM.StepRunning` erase gas bookkeeping
from symbolic states.  They are deliberately parameterized by decoder facts,
so a raw-bytecode proof supplies only a certificate for the bytes at its
current program counter.
-/

namespace Challenge.RouteB.GasStep

open EvmSemantics
open EvmSemantics.EVM
open Challenge.RouteB

/-- Lift one successful `StepRunning` rule into the gas-parametric trace
algebra.  This is the common endpoint used by every opcode-specific symbolic
rule, including submission-specific rules written outside this module. -/
theorem of_running {s t : State} (cost : Nat)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hstep : ∀ gas, cost ≤ gas →
      StepRunning (withGas s gas) (withGas t (gas - cost))) :
    GasSteps s t := by
  apply GasSteps.one cost
  intro gas hgas
  exact Step.running
    (by simpa [withGas] using hrun)
    (by simpa [withGas] using hnp)
    (hstep gas hgas)

theorem add {s : State} {a b : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .ADD)
    (hstack : s.stack = a :: b :: rest)
    (hcap : s.stack.length + Operation.pushArity .ADD ≤
      1024 + Operation.popArity .ADD)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := (a + b) :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .ADD
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.add (withGas s gas) a b rest hop hgas hstack hcap

end Challenge.RouteB.GasStep
