import Challenge.Ripemd160.Submission.Local20261028.ColdPaddingCore2
import Challenge.Ripemd160.Submission.Local20261028.ColdShared32Scratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Local20261028.ColdTrace
import Challenge.Ripemd160.Submission.Local20261028.ColdMain
import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentStart
import Challenge.Ripemd160.Submission.Local20261028.ColdGuardFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadLimitArithmetic
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
/-!
# Direct execution of the RIPEMD-160 padding function (setup, guard, sentinel, footer loop and exit)

The fixed setup and the eight-iteration little-endian footer loop are exposed
as located paths.  The resulting state is shared by correctness and exact gas
accounting.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
open EvmSemantics EvmSemantics.EVM
/-- Residual length after `i` byte-shifts, exactly as the machine holds it. -/
def lengthShift (input : ByteArray) : Nat → UInt256
  | 0 => bitLengthWord input
  | i + 1 => UInt256.shiftRight (lengthShift input i) (UInt256.ofNat 8)

/-- Footer cursor after `i` increments. -/
def lengthAddr (input : ByteArray) : Nat → UInt256
  | 0 => lengthOffsetWord input
  | i + 1 => UInt256.ofNat 1 + lengthAddr input i

/-- The most significant footer byte, written before the loop. -/
def topByteWord (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (bitLengthWord input) (UInt256.ofNat 0x38)

def topByteAddr (input : ByteArray) : UInt256 :=
  UInt256.ofNat 7 + lengthOffsetWord input

def footerStart (input : ByteArray) : Nat :=
  Padding.messageOffset + Padding.paddedLength input.size - 8

def lengthLoopMemory (input : ByteArray) : Nat → ByteArray
  | 0 => (padSentinel input).memory
  | i + 1 => MachineState.writeBytes (lengthLoopMemory input i)
      (ByteArray.mk #[UInt8.ofNat ((lengthShift input i).toNat % 256)])
      (lengthAddr input i).toNat

/-! `activeWords` follows the actual one-byte stores.  In particular, this is
not pre-expanded at loop entry: the first iteration reaches the footer's
last word, and subsequent stores stay in that same word. -/
def lengthLoopActiveWords (input : ByteArray) : Nat → UInt256
  | 0 => (padSentinel input).activeWords
  | i + 1 => UInt256.ofNat (MachineState.activeWordsAfter
      (lengthLoopActiveWords input i).toNat (lengthAddr input i).toNat 1)
def lengthLoopState (input : ByteArray) (i : Nat) : State :=
  { padSentinel input with
    pc := UInt256.ofNat 4583
    stack := lengthAddr input i :: lengthShift input i :: UInt256.ofNat 4583 :: padFrame input
    memory := lengthLoopMemory input i
    activeWords := lengthLoopActiveWords input i }

/-- The footer loop at the end of the executable code (4547..4565): store the low byte, advance
the cursor, shift the residual, and `DUP4 JUMPI` back to the head 4547 that stays under the two
loop registers while the residual is nonzero. -/
def lengthIterationPath : List
    (Challenge.EvmProof.DataStepper.Located Control.Artifact.submissionArtifact .Osaka) :=
  [⟨3351, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3352, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3353, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3354, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3355, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨3356, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3357, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3358, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨3359, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3360, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3361, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3362, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨3363, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def lengthBodyPath := lengthIterationPath.take 10
def lengthBranchPath := lengthIterationPath.drop 10

@[simp] theorem lengthLoopState_halt (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).halt = .Running := by rfl

@[simp] theorem lengthLoopState_fork (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).fork = .Osaka := by rfl

@[simp] theorem lengthLoopState_code (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem lengthLoopState_pc (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).pc = UInt256.ofNat 4583 := by rfl

@[simp] theorem lengthLoopState_stack (input : ByteArray) (i : Nat) :
    (lengthLoopState input i).stack =
      lengthAddr input i :: lengthShift input i :: UInt256.ofNat 4583 :: padFrame input := by rfl

@[simp] theorem padSentinel_code (input : ByteArray) :
    (padSentinel input).executionEnv.code = submissionBytecode := by rfl

/-- State after one low-byte store and both register updates (at the `DUP2` 4559). -/
def lengthSteppedState (input : ByteArray) (i : Nat) : State :=
  { lengthLoopState input i with
    pc := UInt256.ofNat 4595
    stack := lengthAddr input (i + 1) :: lengthShift input (i + 1) :: UInt256.ofNat 4583 ::
      padFrame input
    memory := lengthLoopMemory input (i + 1)
    activeWords := lengthLoopActiveWords input (i + 1) }

def lengthBackReturned (input : ByteArray) (i : Nat) : State :=
  { lengthSteppedState input i with pc := UInt256.ofNat 4583 }

def lengthExitPending (input : ByteArray) (i : Nat) : State :=
  { lengthSteppedState input i with pc := UInt256.ofNat 4598 }

theorem lengthBackReturned_eq (input : ByteArray) (i : Nat) :
    lengthBackReturned input i = lengthLoopState input (i + 1) := by
  unfold lengthBackReturned lengthSteppedState lengthLoopState
  generalize padSentinel input = s
  cases s
  rfl

@[simp] theorem lengthSteppedState_halt (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).halt = .Running := by rfl

@[simp] theorem lengthSteppedState_pc (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).pc = UInt256.ofNat 4595 := by rfl

@[simp] theorem lengthSteppedState_code (input : ByteArray) (i : Nat) :
    (lengthSteppedState input i).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem validLengthLoopHead :
    Decode.isValidJumpDest submissionBytecode 4583 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3351 = 4583 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  rw [← hpc]
  exact Control.Artifact.submissionArtifact.isValidJumpDest_index 3351 (by rfl)

theorem validJump4949 :
    Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 4583).toNat = true :=
  validLengthLoopHead

theorem validJump198 :
    Decode.isValidJumpDest submissionBytecode 198 = true := by
  have hpc : Control.Artifact.submissionArtifact.instructionPC 97 = 198 := padPc116
  rw [← hpc]
  exact Control.Artifact.submissionArtifact.isValidJumpDest_index 97 (by rfl)

theorem validJump461 :
    Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 461).toNat = true :=
  Control.Artifact.validJumpDest_loop

/-! ## Arithmetic bridge for the masked bit length -/

theorem shiftLeft_ofNat_wrap {value shift : Nat}
    (hvalue : value < 2 ^ 256) (hshift : shift < 256) :
    UInt256.shiftLeft (UInt256.ofNat value) (UInt256.ofNat shift) =
      UInt256.ofNat ((value * 2 ^ shift) % 2 ^ 256) := by
  have hshift256 : shift < 2 ^ 256 := Nat.lt_trans hshift (by norm_num)
  have hshiftWord : (UInt256.ofNat shift).toNat = shift := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hshift256]
  unfold UInt256.shiftLeft
  rw [if_neg (by omega), hshiftWord, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hvalue, Nat.shiftLeft_eq,
    show UInt256.size = 2 ^ 256 by rfl]


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.PaddingTrace
