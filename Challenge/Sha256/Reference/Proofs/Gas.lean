import Challenge.Sha256.AdditionalGoals.GasSchedule
import Challenge.Sha256.Reference.Proofs.Bytecode.GasCost

set_option warningAsError true
set_option maxRecDepth 100000

/-!
# Exact gas schedule for the bundled reference

The functional-correctness and gas claims use the same direct execution
certificate for the frozen reference bytecode.  The theorem below exposes its
exact cost as a function of calldata length.
-/

namespace Challenge.Sha256.Reference.Proofs.Gas

open Challenge.Sha256
open EvmSemantics EvmSemantics.EVM
open Challenge.Sha256.Reference.Proofs.Bytecode

/-- Symbolic form of the reference gas schedule used by the leaderboard. -/
def gasFormula : GasFormula :=
  let blocks := (GasFormula.calldataSize + 72) / 64
  1747 + 155996 * blocks + 3 * ((GasFormula.calldataSize + 31) / 32) +
    .memoryCost (90 + 2 * blocks)

/-- Exact gas consumed by the bundled reference on an input of `n` bytes. -/
def gasSchedule : Nat → Nat := gasFormula.eval

theorem blockCount_eq (input : ByteArray) :
    Driver.blockCount input = (input.size + 72) / 64 := by
  simp [Driver.blockCount, Padding.paddedLength]

/-- The displayed schedule is sufficient for every realizable calldata value
of the given length. -/
theorem gasSchedule_correct :
    CorrectWithSchedule referenceBytecode gasSchedule := by
  intro input hfit gas hgas
  let trace := ReferenceCorrect.gasSteps_finalState input hfit
  have htraceCost : trace.cost =
      (Driver.gasSteps_reference input hfit).cost := by
    rfl
  have hcost : trace.cost = gasSchedule input.size := by
    change trace.cost =
      1747 + 155996 * ((input.size + 72) / 64) +
        3 * ((input.size + 31) / 32) +
        MachineState.memCost (90 + 2 * ((input.size + 72) / 64))
    rw [htraceCost]
    simpa [GasCost.referenceGas, blockCount_eq] using
      GasCost.gasSteps_reference_cost input hfit
  have htrace : Steps (initialState referenceBytecode input gas)
      (Challenge.EvmProof.withGas (ReferenceCorrect.finalState input)
        (gas - gasSchedule input.size)) := by
    have hs := trace.trace gas (by simpa [hcost] using hgas)
    simpa [trace, ReferenceCorrect.withGas_initialState_zero, hcost] using hs
  have heval := Challenge.EvmProof.eval_of_steps htrace (by
    change (ReferenceCorrect.finalState input).isDone = true
    exact ReferenceCorrect.finalState_isDone input)
  have hresult :
      (Challenge.EvmProof.withGas (ReferenceCorrect.finalState input)
        (gas - gasSchedule input.size)).toResult =
          .returned (spec input) := by
    change (ReferenceCorrect.finalState input).toResult = .returned (spec input)
    exact ReferenceCorrect.finalState_toResult input hfit
  simpa [hresult] using heval

end Challenge.Sha256.Reference.Proofs.Gas
