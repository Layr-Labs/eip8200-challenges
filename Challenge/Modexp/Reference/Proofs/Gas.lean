import Challenge.Modexp.AdditionalGoals.GasSchedule
import Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect
import Challenge.Modexp.Reference.Proofs.Bytecode.MemoryHighWater

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

/-!
# Exact gas schedule for the bundled reference

The symbolic formula mirrors the four successful bytecode branches and is
proved against the same direct execution certificate as functional
correctness. `B`, `E`, and `M` are the decoded operand byte lengths, `V_M` is
the padded modulus value, and `N = ⌈M / 32⌉` is the limb count.
-/

namespace Challenge.Modexp.Reference.Proofs.Gas

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Reference.Proofs.Bytecode

/-- Symbolic exact gas consumed by the frozen reference bytecode. -/
def gasFormula : GasFormula :=
  let b := GasFormula.baseSize
  let e := GasFormula.exponentSize
  let m := GasFormula.modulusSize
  let modulus := GasFormula.modulusValue
  let limbs := (m + 31) / 32
  let finalMemory := GasFormula.memoryCost (192 + limbs)
  let bigZero :=
    253 + ((343 + limbs * 284 + m * 190) + (56 + limbs * 74)) +
      finalMemory
  let bigNonzero :=
    253 +
      ((343 + limbs * 284 + m * 190) +
       (50 + limbs * 74) +
       (77 + limbs * 71) +
       (b * (3506 + limbs * 7248) + (206 + limbs * 453)) +
       3 +
       e * (106 + 8 *
         (613 + limbs * 526 +
           2 * (limbs * (102 + 256 * (426 + limbs * 906))))) +
       (66 + m * 138)) +
      finalMemory
  .ifZero m 183
    (.ifLe m 32
      (.ifZero modulus 950 (1053 + 140 * b + 1210 * e))
      (.ifZero modulus bigZero bigNonzero))

/-- Executable form of `gasFormula`. -/
def gasSchedule : ByteArray → Nat := gasFormula.eval

/-- The symbolic schedule is the exact cost of the certified bytecode trace. -/
theorem gasSchedule_eq_referenceGas (input : ByteArray)
    (hvalid : ValidInput input) :
    gasSchedule input = ReferenceCorrect.referenceGas input := by
  have hmodulus : modulusValue input = Word.modulusValue input := by
    simp [Challenge.Modexp.modulusValue, Word.modulusValue,
      Word.modulusOffset, Word.expOffset]
  by_cases hzeroSize : modulusSize input = 0
  · simp [gasSchedule, gasFormula, GasFormula.eval,
      ReferenceCorrect.referenceGas, hzeroSize]
  by_cases hword : modulusSize input ≤ 32
  · by_cases hzeroModulus : modulusValue input = 0
    · simp [gasSchedule, gasFormula, GasFormula.eval,
        ReferenceCorrect.referenceGas, hzeroSize, hword, hzeroModulus,
        ← hmodulus]
    · simp [gasSchedule, gasFormula, GasFormula.eval,
        ReferenceCorrect.referenceGas, hzeroSize, hword, hzeroModulus,
        ← hmodulus, WordGas.wordGas]
  · have hbig : 32 < modulusSize input := by omega
    by_cases hzeroModulus : modulusValue input = 0
    · have hmemory := bigZeroFinalState_activeWords input hvalid hbig
      simp [gasSchedule, gasFormula, GasFormula.eval,
        ReferenceCorrect.referenceGas, hzeroSize, hword, hzeroModulus,
        ← hmodulus, BigZeroCorrect.zeroWork, Limbs.limbCount,
        hmemory]
    · have hmemory := bigCompletedState_activeWords input hvalid hbig
      simp [gasSchedule, gasFormula, GasFormula.eval,
        ReferenceCorrect.referenceGas, hzeroSize, hword, hzeroModulus,
        ← hmodulus, BigComplete.nonzeroWork, Limbs.limbCount,
        hmemory]

/-- The displayed exact schedule suffices for every valid MODEXP tuple. -/
theorem gasSchedule_correct :
    CorrectWithSchedule referenceBytecode gasSchedule := by
  intro input hvalid gas hgas
  let trace := ReferenceCorrect.gasSteps_reference input hvalid
  have hcost : trace.cost = gasSchedule input := by
    rw [show trace.cost = ReferenceCorrect.referenceGas input by
      simpa [trace] using ReferenceCorrect.gasSteps_reference_cost input hvalid]
    exact (gasSchedule_eq_referenceGas input hvalid).symm
  have htrace : Steps (initialState referenceBytecode input gas)
      (Challenge.EvmProof.withGas (ReferenceCorrect.finalState input)
        (gas - gasSchedule input)) := by
    have hs := trace.trace gas (by simpa [hcost] using hgas)
    simpa [trace, ReferenceCorrect.withGas_initialState_zero, hcost] using hs
  have heval := Challenge.EvmProof.eval_of_steps htrace
    (ReferenceCorrect.finalState_isDone input)
  have hresult :
      (Challenge.EvmProof.withGas (ReferenceCorrect.finalState input)
        (gas - gasSchedule input)).toResult = .returned (spec input) := by
    change (ReferenceCorrect.finalState input).toResult = .returned (spec input)
    exact ReferenceCorrect.finalState_result input hvalid
  simpa [hresult] using heval

end Challenge.Modexp.Reference.Proofs.Gas
