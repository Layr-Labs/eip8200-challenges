import Challenge.Modexp.Submission.Proofs.Fast.GuardLogic
import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardState

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardLogic

abbrev entryState (input : ByteArray) : State := Main.trampolineState input 3133
abbrev fallbackState (input : ByteArray) : State := Main.trampolineState input 1314

def branchState (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def conditionState (input : ByteArray) (pc : Nat) (condition : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [condition] }

def jumpStackState (input : ByteArray) (condition : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 3916
      stack := [UInt256.ofNat 3921, condition] }

def accState (input : ByteArray) (pc : Nat) (acc : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [acc] }

def chunk0 := GuardData.checks.take 4
def chunk1 := (GuardData.checks.drop 4).take 4
def chunk2 := (GuardData.checks.drop 8).take 4
def chunk3 := (GuardData.checks.drop 12).take 4
def chunk4 := GuardData.checks.drop 16

def acc0 (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.xor (UInt256.ofNat input.size) (UInt256.ofNat 611)) 0
def acc1 (input : ByteArray) := scanDiff input chunk0 (acc0 input)
def acc2 (input : ByteArray) := scanDiff input chunk1 (acc1 input)
def acc3 (input : ByteArray) := scanDiff input chunk2 (acc2 input)
def acc4 (input : ByteArray) := scanDiff input chunk3 (acc3 input)
def acc5 (input : ByteArray) := scanDiff input chunk4 (acc4 input)

theorem acc5_eq_guardDiff (input : ByteArray) : acc5 input = guardDiff input := by rfl

def storeWord (mem : ByteArray) (addr : Nat) (w : UInt256) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w.toNat 32) addr

def answerMemory : ByteArray :=
  storeWord (storeWord (storeWord (storeWord
    (storeWord (storeWord (storeWord (storeWord ByteArray.empty
      0 36457779276215628618107628175862952880503802480134169461413915661242852128650)
      32 87049543137291641647099327099349755118393366951315864702186066057471381150321)
      64 100461675459921706400033383628344108228127659798054063115947067974792041444897)
      96 92652640243433598898841338411780137466704615812747125847068622118856402577117)
      128 14159211218075883537326960255904060289806489979180585240426546259839689087273)
      160 67818750046613989747287612287447883644842343144736888277507620664030220336931)
      192 2618339351906218248436954888076772231186051744572579598192995074227528865064)
      224 9746032139171987504721760760529593857951721070820754662511731733855650243837

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 4213
      memory := answerMemory
      activeWords := UInt256.ofNat 8
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 0 256 }

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

end Challenge.Modexp.Submission.Proofs.Fast.GuardState
