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
  [Main.opAt 1826 .JUMPDEST,
   Main.opAt 1827 (.Dup ⟨0, by decide⟩),
   Main.pushAt 1828 1 32,
   Main.opAt 1829 .XOR,
   Main.opAt 1830 (.Dup ⟨2, by decide⟩),
   Main.pushAt 1831 1 32,
   Main.opAt 1832 .XOR,
   Main.opAt 1833 .OR,
   Main.opAt 1834 (.Dup ⟨3, by decide⟩),
   Main.pushAt 1835 1 32,
   Main.opAt 1836 .XOR,
   Main.opAt 1837 .OR,
   Main.opAt 1838 .ISZERO]

def branchPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1839 2 5233, Main.opAt 1840 .JUMPI]

def missPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1841 2 5323, Main.opAt 1842 .JUMP]

def exactCheckPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 3845 .JUMPDEST,
   Main.opAt 3846 (.Dup ⟨0, by decide⟩), Main.pushAt 3847 1 1,
   Main.opAt 3848 .XOR,
   Main.opAt 3849 (.Dup ⟨2, by decide⟩), Main.pushAt 3850 1 1,
   Main.opAt 3851 .XOR, Main.opAt 3852 .OR,
   Main.opAt 3853 (.Dup ⟨3, by decide⟩), Main.pushAt 3854 1 1,
   Main.opAt 3855 .XOR, Main.opAt 3856 .OR,
   Main.opAt 3857 (.Dup ⟨4, by decide⟩), Main.opAt 3858 .CALLDATALOAD,
   Main.pushAt 3859 0 0, Main.opAt 3860 .BYTE, Main.pushAt 3861 1 2,
   Main.opAt 3862 .XOR, Main.opAt 3863 .OR,
   Main.opAt 3864 (.Dup ⟨5, by decide⟩), Main.opAt 3865 .CALLDATALOAD,
   Main.pushAt 3866 0 0, Main.opAt 3867 .BYTE, Main.pushAt 3868 1 5,
   Main.opAt 3869 .XOR, Main.opAt 3870 .OR,
   Main.opAt 3871 (.Dup ⟨6, by decide⟩), Main.opAt 3872 .CALLDATALOAD,
   Main.pushAt 3873 0 0, Main.opAt 3874 .BYTE, Main.pushAt 3875 1 13,
   Main.opAt 3876 .XOR, Main.opAt 3877 .OR,
   Main.opAt 3878 .ISZERO, Main.pushAt 3879 2 5371,
   Main.opAt 3880 .JUMPI]

def exactFallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 3881 2 517, Main.opAt 3882 .JUMP]

def exactReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 3883 .JUMPDEST, Main.pushAt 3884 1 6, Main.pushAt 3885 0 0,
   Main.opAt 3886 .MSTORE8, Main.pushAt 3887 1 1, Main.pushAt 3888 0 0,
   Main.opAt 3889 .RETURN]

/-- The first instruction on the fixed-width hit path. -/
def hitEntryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 1843 .JUMPDEST]

@[simp] theorem routePCs (i : Nat)
    (hlo : 1826 ≤ i) (hhi : i ≤ 1843) :
    Artifact.submissionArtifact.instructionPC i =
      ([2613,2614,2616,2617,2618,2619,2621,2622,2623,2624,2626,2627,2628,
       2629,2632,2633,2636,2637] : List Nat)[i - 1826]! := by
  interval_cases i <;> decide

@[simp] theorem jump3024 :
    Decode.isValidJumpDest submissionBytecode 2637 = true :=
  Artifact.isValidJumpDest_index 1843 (by rfl)

@[simp] theorem jump517 :
    Decode.isValidJumpDest submissionBytecode 517 = true :=
  Artifact.isValidJumpDest_index 415 (by rfl)
@[simp] theorem jumpExactEntry :
    Decode.isValidJumpDest submissionBytecode 5323 = true :=
  Artifact.isValidJumpDest_index 3845 (by rfl)

@[simp] theorem jumpExactReturn :
    Decode.isValidJumpDest submissionBytecode 5371 = true :=
  Artifact.isValidJumpDest_index 3883 (by rfl)

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
    pc := UInt256.ofNat 2629
    stack := UInt256.isZero (WindowGuardLogic.guardDiff input) :: routeStack input }

/-- State after the untaken conditional branch, before the legacy jump. -/
def missState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 2633 }

/-- State after the taken conditional branch, before consuming the hit
`JUMPDEST`.  The guard preserves the dispatcher calling-convention stack. -/
def hitState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with pc := UInt256.ofNat 2637 }

theorem routeStack_eq_entry (input : ByteArray) :
    routeStack input = (Dispatch.wordEntryState input).stack := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs
