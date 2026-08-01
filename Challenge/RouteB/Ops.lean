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

theorem jumpdest {s : State}
    (hop : s.decodedOp = some .JUMPDEST)
    (hcap : s.stack.length + Operation.pushArity .JUMPDEST ≤
      1024 + Operation.popArity .JUMPDEST)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .JUMPDEST
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.jumpdest (withGas s gas) hop hgas hcap

theorem push0 {s : State}
    (hop : s.decodedOp = some (.Push ⟨0, by decide⟩))
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := ⟨0⟩ :: s.stack, pc := s.pc.succ } := by
  let op : Operation := .Push ⟨0, by decide⟩
  let cost := Gas.baseCost s.fork op
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, op] using
    StepRunning.push0 (withGas s gas) hop hgas hcap

theorem pushN {s : State} (k : Fin 33) (data : UInt256) (immWidth : Nat)
    (hk : 0 < k.val)
    (hdecoded : s.decoded =
      some (.Push ⟨k, k.isLt⟩, some (data, immWidth)))
    (hcap : s.stack.length < 1024)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := data :: s.stack
      pc := s.pc + UInt256.ofNat (immWidth + 1) } := by
  let op : Operation := .Push ⟨k, k.isLt⟩
  let cost := Gas.baseCost s.fork op
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, op] using
    StepRunning.pushN (withGas s gas) k data immWidth hk hdecoded hgas hcap

theorem mstore {s : State} (offset value : UInt256) (rest : List UInt256)
    (hop : s.decodedOp = some .MSTORE)
    (hstack : s.stack = offset :: value :: rest)
    (hcap : s.stack.length + Operation.pushArity .MSTORE ≤
      1024 + Operation.popArity .MSTORE)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with
      stack := rest
      pc := s.pc.succ
      memory := MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded value.toNat 32) offset.toNat
      activeWords := s.activeWordsAfterUInt256 offset.toNat 32 } := by
  let cost := Gas.mstoreTotal s offset
  apply of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost, Gas.mstoreTotal, State.activeWordsAfterUInt256] using
    StepRunning.mstore (withGas s gas) offset value rest hop hstack hgas hcap

end Challenge.RouteB.GasStep
