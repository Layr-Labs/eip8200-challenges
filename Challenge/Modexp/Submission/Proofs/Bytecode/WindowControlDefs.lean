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
  [Main.pushAt 1844 2 5372, Main.opAt 1845 .JUMPI]

def missPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.pushAt 1846 2 517, Main.opAt 1847 .JUMP]
/-- The new fixed-width shortcut entry checks a zero base against a
nonzero exponent before the existing table path. -/
def baseZeroGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 3268 .JUMPDEST,
   Main.pushAt 3269 1 96,
   Main.opAt 3270 .CALLDATALOAD,
   Main.opAt 3271 .ISZERO,
   Main.pushAt 3272 1 128,
   Main.opAt 3273 .CALLDATALOAD,
   Main.opAt 3274 .ISZERO,
   Main.opAt 3275 .ISZERO,
   Main.opAt 3276 .AND,
   Main.pushAt 3277 2 5391,
   Main.opAt 3278 .JUMPI,
   Main.pushAt 3279 2 3024,
   Main.opAt 3280 .JUMP]

def baseZeroHandlerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [Main.opAt 3281 .JUMPDEST,
   Main.pushAt 3282 1 160,
   Main.opAt 3283 .CALLDATALOAD,
   Main.pushAt 3284 2 3563,
   Main.opAt 3285 .JUMP]

@[simp] theorem baseZeroPCs (i : Nat) (hlo : 3268 ≤ i) (hhi : i ≤ 3285) :
    Artifact.submissionArtifact.instructionPC i =
      [5372, 5373, 5375, 5376, 5377, 5379, 5380, 5381, 5382,
       5383, 5386, 5387, 5390, 5391, 5392, 5394, 5395, 5398][i - 3268]! := by
  interval_cases i <;> decide

@[simp] theorem jump5391 :
    Decode.isValidJumpDest submissionBytecode 5391 = true :=
  Artifact.isValidJumpDest_index 3281 (by rfl)
@[simp] theorem jump5372 :
    Decode.isValidJumpDest submissionBytecode 5372 = true :=
  Artifact.isValidJumpDest_index 3268 (by rfl)

@[simp] theorem jump3563 :
    Decode.isValidJumpDest submissionBytecode 3563 = true :=
  Artifact.isValidJumpDest_index 2331 (by rfl)

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

def baseZeroEntryState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 5372
    stack := routeStack input }

def baseZeroHandlerState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 5391
    stack := routeStack input }

def baseZeroReturnState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 3563
    stack := MachineState.readWord input 160 :: routeStack input }

def shortcutBaseWord (input : ByteArray) : UInt256 :=
  MachineState.readWord input 96

def shortcutExponentWord (input : ByteArray) : UInt256 :=
  MachineState.readWord input 128

def baseZeroMatches (input : ByteArray) : Prop :=
  shortcutBaseWord input = 0 ∧ shortcutExponentWord input ≠ 0

theorem routeStack_eq_entry (input : ByteArray) :
    routeStack input = (Dispatch.wordEntryState input).stack := by
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs
