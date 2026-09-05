import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Logic
import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024State

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard1024Logic

abbrev entryState (input : ByteArray) : State := Main.trampolineState input 4214
abbrev fallbackState (input : ByteArray) : State := Main.trampolineState input 4838

def branchState (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def conditionState (input : ByteArray) (pc : Nat) (condition : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [condition] }

def jumpStackState (input : ByteArray) (condition : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4685
      stack := [UInt256.ofNat 4690, condition] }

def accState (input : ByteArray) (pc : Nat) (acc : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [acc] }

def chunk0 := Guard1024Data.checks.take 4
def chunk1 := (Guard1024Data.checks.drop 4).take 4
def chunk2 := Guard1024Data.checks.drop 8

def acc0 (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.xor (UInt256.ofNat input.size) (UInt256.ofNat 353)) 0
def acc1 (input : ByteArray) := scanDiff input chunk0 (acc0 input)
def acc2 (input : ByteArray) := scanDiff input chunk1 (acc1 input)
def acc3 (input : ByteArray) := scanDiff input chunk2 (acc2 input)

theorem acc3_eq_guardDiff (input : ByteArray) : acc3 input = guardDiff input := by rfl

def storeWord (mem : ByteArray) (addr : Nat) (w : UInt256) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w.toNat 32) addr

def answerMemory : ByteArray :=
  storeWord (storeWord (storeWord
    (storeWord ByteArray.empty
      0 15311000363910303241540621865409679537502595890653539278795210471371740305479)
      32 108131171086235498843144070769070390205391711722934919355131028315980221287783)
      64 30211351789909815513928503188859640991933128769084385520359151767836288201668)
      96 19240783075872300903671752229116273808210541663683986574655295206487138977467

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4837
      memory := answerMemory
      activeWords := UInt256.ofNat 4
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 0 128 }

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

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024State
