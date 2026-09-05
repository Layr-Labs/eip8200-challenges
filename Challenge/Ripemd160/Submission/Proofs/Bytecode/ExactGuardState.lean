import Challenge.Ripemd160.Submission.Bytecode
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.EvmProof.Word

set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

/-!
# States for the compact exact `1000 a's` guard

The loop keeps `[difference, offset, fullWord]` on the stack.  Reusing the one
full-word constant is the code-size optimization that reduces the appended
guard from 327 bytes to 145 bytes.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardState

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Ripemd160
open ExactGuardData ExactGuardLogic ExactGuardSpec

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

abbrev entryState (input : ByteArray) : State := atPC input 0x1492
abbrev fallbackState (input : ByteArray) : State := atPC input 0x03ee
abbrev branchState (input : ByteArray) (pc : Nat) : State := atPC input pc

/-- Loop header invariant at PC `0x14bd`. -/
def loopState (input : ByteArray) (offset : Nat)
    (difference : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 0x14bd
      stack := [difference, UInt256.ofNat offset, fullWord] }

/-- Not-taken loop exit, retaining offset 992 until the two-op exit cleanup. -/
def loopExitState (input : ByteArray) (offset : Nat)
    (difference : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 0x14d3
      stack := [difference, UInt256.ofNat offset, fullWord] }

/-- State after the loop offset has been removed, while `fullWord` is retained. -/
def accState (input : ByteArray) (pc : Nat)
    (difference : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [difference, fullWord] }

/-- State after the shared full-word constant has also been removed. -/
def diffState (input : ByteArray) (pc : Nat)
    (difference : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [difference] }

def conditionState (input : ByteArray) (pc : Nat)
    (condition : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [condition] }

def jumpStackState (input : ByteArray) (condition : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 0x1502
      stack := [UInt256.ofNat 0x1507, condition] }

/-- Difference contributed by the calldata-size comparison. -/
def acc0 (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.xor (UInt256.ofNat input.size) (UInt256.ofNat 1000)) 0

/-- Difference after `n` complete full-word iterations. -/
def acc (input : ByteArray) : Nat → UInt256
  | 0 => acc0 input
  | n + 1 => UInt256.lor
      (UInt256.xor (MachineState.readWord input (32 * n)) fullWord)
      (acc input n)

/-- Difference after the separately encoded padded tail check. -/
def tailAcc (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.xor (MachineState.readWord input 992) tailWord)
    (acc input 31)

/-- Thirty-one loop iterations and the tail are the declarative guard scan. -/
theorem tailAcc_eq_guardDiff (input : ByteArray) :
    tailAcc input = guardDiff input := by rfl

def storeWord (memory : ByteArray) (address : Nat)
    (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 0x1522
      memory := answerMemory
      activeWords := UInt256.ofNat 1
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 0 32 }

theorem diff_isZero_one (input : ByteArray) (h : guardDiff input = 0) :
    UInt256.isZero (guardDiff input) = UInt256.ofNat 1 := by
  rw [h]
  decide

theorem diff_isZero_zero (input : ByteArray) (h : guardDiff input ≠ 0) :
    UInt256.isZero (guardDiff input) = UInt256.ofNat 0 := by
  have hnat : (guardDiff input).toNat ≠ 0 := by
    intro hz
    apply h
    apply Challenge.EvmProof.Word.word_ext
    rw [show (0 : UInt256).toNat = 0 by decide]
    exact hz
  simp [UInt256.isZero, hnat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardState
