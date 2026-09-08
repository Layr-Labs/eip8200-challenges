import Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Fixed-width route control-flow definitions

Artifact-bound paths and gas-erased states for the width guard at pc 3000.
The execution proofs are intentionally split from these definitions so each
short segment can be elaborated independently.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs

open EvmSemantics
open EvmSemantics.EVM

def guardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1828 .JUMPDEST,
   Main.opAt 1829 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1830 1 32,
   Main.opAt 1831 .XOR,
   Main.opAt 1832 (.Dup ⟨2, by decide⟩),
   Main.pushAt 1833 1 32,
   Main.opAt 1834 .XOR,
   Main.opAt 1835 .OR,
   Main.opAt 1836 (.Dup ⟨3, by decide⟩),
   Main.pushAt 1837 1 32,
   Main.opAt 1838 .XOR,
   Main.opAt 1839 .OR,
   Main.opAt 1840 .ISZERO]

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1841 2 2809, Main.opAt 1842 .JUMPI]

def missPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1843 2 517, Main.opAt 1844 .JUMP]

/-- The first instruction on the fixed-width hit path. -/
def hitEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1845 .JUMPDEST]

@[simp] theorem routePCs (i : Nat)
    (hlo : 1828 ≤ i) (hhi : i ≤ 1845) :
    Artifact.submissionArtifact.instructionPC i =
      ([2785,2786,2787,2789,2790,2791,2793,2794,2795,2796,2798,2799,2800,2801,2804,2805,2808,2809] : List Nat)[i - 1828]! := by
  interval_cases i <;> decide

@[simp] theorem jump3024 :
    Decode.isValidJumpDest submissionBytecode 2809 = true :=
  Artifact.isValidJumpDest_index 1845 (by rfl)

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
    pc := UInt256.ofNat 2801
    stack := UInt256.isZero (WindowGuardLogic.guardDiff input) :: routeStack input }

/-- State after the untaken conditional branch, before the legacy jump. -/
def missState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 2805 }

/-- State after the taken conditional branch, before consuming the hit
`JUMPDEST`.  The guard preserves the dispatcher calling-convention stack. -/
def hitState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 2809 }

theorem routeStack_eq_entry (input : ByteArray) :
    routeStack input = (Dispatch.wordEntryState input).stack := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs
