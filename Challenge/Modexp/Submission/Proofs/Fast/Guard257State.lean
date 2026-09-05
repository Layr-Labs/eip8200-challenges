import Challenge.Modexp.Submission.Proofs.Fast.Guard257Logic
import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257State

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard257Logic

abbrev entryState (input : ByteArray) : State := Main.trampolineState input 4838
abbrev fallbackState (input : ByteArray) : State := Main.trampolineState input 5157

def branchState (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def conditionState (input : ByteArray) (pc : Nat) (condition : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [condition] }

def jumpStackState (input : ByteArray) (condition : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 5076
      stack := [UInt256.ofNat 5081, condition] }

def accState (input : ByteArray) (pc : Nat) (acc : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [acc] }

def chunk0 := Guard257Data.checks.take 3
def chunk1 := Guard257Data.checks.drop 3

def acc0 (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.xor (UInt256.ofNat input.size) (UInt256.ofNat 163)) 0
def acc1 (input : ByteArray) := scanDiff input chunk0 (acc0 input)
def acc2 (input : ByteArray) := scanDiff input chunk1 (acc1 input)

theorem acc2_eq_guardDiff (input : ByteArray) : acc2 input = guardDiff input := by rfl

def storeWord (mem : ByteArray) (addr : Nat) (w : UInt256) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w.toNat 32) addr

def answerMemory : ByteArray :=
  storeWord (storeWord ByteArray.empty
    0 452312848583266388373324160190187140051835877600158453279131187530910662655)
    32 115339776388732929035197660848497720713218148788040405586178452820382218977280

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 5156
      memory := answerMemory
      activeWords := UInt256.ofNat 2
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 0 33 }

theorem diff_isZero_one (input : ByteArray) (h : guardDiff input = 0) :
    UInt256.isZero (guardDiff input) = UInt256.ofNat 1 := by rw [h]; decide

theorem diff_isZero_zero (input : ByteArray) (h : guardDiff input ≠ 0) :
    UInt256.isZero (guardDiff input) = UInt256.ofNat 0 := by
  have hnat : (guardDiff input).toNat ≠ 0 := by
    intro hz
    apply h
    apply Challenge.EvmProof.Word.word_ext
    rw [show (0 : UInt256).toNat = 0 by decide]
    exact hz
  simp [UInt256.isZero, hnat]

end Challenge.Modexp.Submission.Proofs.Fast.Guard257State
