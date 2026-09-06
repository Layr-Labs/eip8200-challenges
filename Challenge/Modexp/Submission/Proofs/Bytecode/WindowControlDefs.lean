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
  [Main.opAt 1831 .JUMPDEST,
   Main.opAt 1832 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1833 1 32,
   Main.opAt 1834 .XOR,
   Main.opAt 1835 (.Dup ⟨2, by decide⟩),
   Main.pushAt 1836 1 32,
   Main.opAt 1837 .XOR,
   Main.opAt 1838 .OR,
   Main.opAt 1839 (.Dup ⟨3, by decide⟩),
   Main.pushAt 1840 1 32,
   Main.opAt 1841 .XOR,
   Main.opAt 1842 .OR,
   Main.opAt 1843 .ISZERO]

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1844 2 3024, Main.opAt 1845 .JUMPI]

def missPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1846 2 517, Main.opAt 1847 .JUMP]

/-- The first instruction on the fixed-width hit path. -/
def hitEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1848 .JUMPDEST]

@[simp] theorem routePCs (i : Nat) (hlo : 1831 ≤ i) (hhi : i ≤ 1848) :
    Artifact.submissionArtifact.instructionPC i =
      [3000, 3001, 3002, 3004, 3005, 3006, 3008, 3009, 3010,
       3011, 3013, 3014, 3015, 3016, 3019, 3020, 3023, 3024][i - 1831]! := by
  interval_cases i <;> decide

@[simp] theorem jump3024 :
    Decode.isValidJumpDest submissionBytecode 3024 = true :=
  Artifact.isValidJumpDest_index 1848 (by rfl)

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
    pc := UInt256.ofNat 3016
    stack := UInt256.isZero (WindowGuardLogic.guardDiff input) :: routeStack input }

/-- State after the untaken conditional branch, before the legacy jump. -/
def missState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 3020 }

/-- State after the taken conditional branch, before consuming the hit
`JUMPDEST`.  The guard preserves the dispatcher calling-convention stack. -/
def hitState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 3024 }

theorem routeStack_eq_entry (input : ByteArray) :
    routeStack input = (Dispatch.wordEntryState input).stack := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs
