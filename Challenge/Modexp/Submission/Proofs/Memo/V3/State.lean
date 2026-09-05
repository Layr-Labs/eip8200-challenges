import Challenge.Modexp.Submission.Proofs.Memo.Dispatch
import Challenge.Modexp.Submission.Proofs.Memo.V3.Data

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V3.State

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic

def accState (input : ByteArray) (pc : Nat) (acc : UInt256) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat pc
      stack := [acc] }

def acc0 (input : ByteArray) : UInt256 :=
  UInt256.xor (MachineState.readWord input 94) (290062066191873733550822415321244206417662036842114019324193742671314944 : UInt256)

theorem acc0_eq_guardDiff (input : ByteArray) :
    acc0 input = guardDiff Data.checks input := by rfl

def storeWord (mem : ByteArray) (addr w : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) addr

def answerMemory : ByteArray :=
  ByteArray.empty

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1642
      stack := []
      memory := answerMemory
      activeWords := UInt256.ofNat 0
      halt := .Returned
      hReturn := MachineState.readPadded answerMemory 0 0 }

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 0 = ByteArray.empty := by
  decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.V3.State
