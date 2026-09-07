import Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-!
# Fixed-width route control-flow definitions

Artifact-bound paths and gas-erased states for the width guard at pc 3029.
The execution proofs are intentionally split from these definitions so each
short segment can be elaborated independently.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs

open EvmSemantics
open EvmSemantics.EVM

def guardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1856 .JUMPDEST,
   Main.opAt 1857 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1858 1 32,
   Main.opAt 1859 .XOR,
   Main.opAt 1860 (.Dup ⟨2, by decide⟩),
   Main.pushAt 1861 1 32,
   Main.opAt 1862 .XOR,
   Main.opAt 1863 .OR,
   Main.opAt 1864 (.Dup ⟨3, by decide⟩),
   Main.pushAt 1865 1 32,
   Main.opAt 1866 .XOR,
   Main.opAt 1867 .OR,
   Main.opAt 1868 .ISZERO]

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1869 2 3053, Main.opAt 1870 .JUMPI]

def missPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1871 2 517, Main.opAt 1872 .JUMP]

/-- The first instruction on the fixed-width hit path. -/
def hitEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1873 .JUMPDEST]

@[simp] theorem routePCs (i : Nat) (hlo : 1856 ≤ i) (hhi : i ≤ 1873) :
    Artifact.submissionArtifact.instructionPC i =
      [3029, 3030, 3031, 3033, 3034, 3035, 3037, 3038, 3039,
       3040, 3042, 3043, 3044, 3045, 3048, 3049, 3052, 3053][i - 1856]! := by
  interval_cases i <;> decide

@[simp] theorem jump3053 :
    Decode.isValidJumpDest submissionBytecode 3053 = true :=
  Artifact.isValidJumpDest_index 1873 (by rfl)

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
    pc := UInt256.ofNat 3045
    stack := UInt256.isZero (WindowGuardLogic.guardDiff input) :: routeStack input }

/-- State after the untaken conditional branch, before the legacy jump. -/
def missState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 3049 }

/-- State after the taken conditional branch, before consuming the hit
`JUMPDEST`.  The guard preserves the dispatcher calling-convention stack. -/
def hitState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 3053 }

theorem routeStack_eq_entry (input : ByteArray) :
    routeStack input = (Dispatch.wordEntryState input).stack := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs
