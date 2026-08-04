import Challenge.Modexp.AdditionalGoals.GasSchedule
import Challenge.Modexp.Reference.Proofs.Bytecode.ReferenceCorrect

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

end Challenge.Modexp.Reference.Proofs.Gas
