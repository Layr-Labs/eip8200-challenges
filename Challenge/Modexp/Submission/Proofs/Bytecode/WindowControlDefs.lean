import Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Fixed-width route control-flow definitions

Artifact-bound paths and gas-erased states for the width guard at pc 2638.
The execution proofs are intentionally split from these definitions so each
short segment can be elaborated independently.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs

open EvmSemantics
open EvmSemantics.EVM

def guardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1833 .JUMPDEST,
   Main.opAt 1834 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1835 1 32,
   Main.opAt 1836 .XOR,
   Main.opAt 1837 (.Dup ⟨2, by decide⟩),
   Main.pushAt 1838 1 32,
   Main.opAt 1839 .XOR,
   Main.opAt 1840 .OR,
   Main.opAt 1841 (.Dup ⟨3, by decide⟩),
   Main.pushAt 1842 1 32,
   Main.opAt 1843 .XOR,
   Main.opAt 1844 .OR,
   Main.opAt 1845 .ISZERO]

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1846 2 2657, Main.opAt 1847 .JUMPI]

def missPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1848 2 517, Main.opAt 1849 .JUMP]

/-- The first instruction on the fixed-width hit path. -/
def hitEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1850 .JUMPDEST]

@[simp] theorem routePCs (i : Nat)
    (hlo : 1833 ≤ i) (hhi : i ≤ 1850) :
    Artifact.submissionArtifact.instructionPC i =
      ([2633,2634,2635,2637,2638,2639,2641,2642,2643,2644,2646,2647,2648,2649,2652,2653,2656,2657] : List Nat)[i - 1833]! := by
  interval_cases i <;> decide

@[simp] theorem jump3024 :
    Decode.isValidJumpDest submissionBytecode 2657 = true :=
  Artifact.isValidJumpDest_index 1850 (by rfl)

@[simp] theorem jump517 :
    Decode.isValidJumpDest submissionBytecode 517 = true :=
  Artifact.isValidJumpDest_index 415 (by rfl)

def routeStack (input : ByteArray) : List UInt256 :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
   UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
   UInt256.ofNat 1267, UInt256.ofNat modOff, UInt256.ofNat expOff,
   UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b]

/-- State after the three width comparisons and the final `ISZERO`. -/
def conditionState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 2649
    stack := UInt256.isZero (WindowGuardLogic.guardDiff input) :: routeStack input }

/-- State after the untaken conditional branch, before the legacy jump. -/
def missState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 2653 }

/-- State after the taken conditional branch, before consuming the hit
`JUMPDEST`.  The guard preserves the dispatcher calling-convention stack. -/
def hitState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 2657 }

theorem routeStack_eq_entry (input : ByteArray) :
    routeStack input = (Dispatch.wordEntryState input).stack := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs
