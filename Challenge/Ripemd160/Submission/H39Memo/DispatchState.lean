import Challenge.EvmProof.Stepper

set_option warningAsError true
set_option maxRecDepth 40000

namespace Challenge.Ripemd160.Submission.H39Memo.DispatchState

open EvmSemantics
open EvmSemantics.EVM

def guardPC : Nat := 1671
def fallbackPC : Nat := 1006
def fallbackAfterJumpPC : Nat := 1007
def emptyPC : Nat := 3264
def abcPC : Nat := 3293
def patternPC : Nat := 1696

def atPC (s : State) (pc : Nat) (stack : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc, stack := stack }

def guardEntry (s : State) : State :=
  atPC s guardPC []

def afterSizeCheck (s : State) (pc size : Nat) : State :=
  atPC s pc [UInt256.ofNat size]

def emptyEntry (s : State) : State :=
  afterSizeCheck s emptyPC 0

def abcEntry (s : State) : State :=
  afterSizeCheck s abcPC 3

def patternEntry (s : State) (pc size : Nat) : State :=
  afterSizeCheck s pc size

def outputEntry (s : State) (pc : Nat) : State :=
  atPC s pc []

def fallbackJumpDestEntry (s : State) : State :=
  atPC s fallbackPC []

def fallbackEntry (s : State) : State :=
  atPC s fallbackAfterJumpPC []

def returned (s : State) (returnPC : Nat) (digest : UInt256) : State :=
  let memory := MachineState.writeBytes s.memory
    (Data.Bytes.natToBytesPadded digest.toNat 32) 0
  let activeWordsAfterMStore := s.activeWordsAfterUInt256 0 32
  let activeWordsAfterReturn := UInt256.ofNat
    (MachineState.activeWordsAfter activeWordsAfterMStore.toNat 0 32)
  { s with
    pc := UInt256.ofNat returnPC
    stack := []
    halt := .Returned
    memory := memory
    hReturn := MachineState.readPadded memory 0 32
    activeWords := activeWordsAfterReturn }

@[simp] theorem atPC_pc (s : State) (pc : Nat) (stack : List UInt256) :
    (atPC s pc stack).pc = UInt256.ofNat pc := by rfl

@[simp] theorem atPC_stack (s : State) (pc : Nat) (stack : List UInt256) :
    (atPC s pc stack).stack = stack := by rfl

@[simp] theorem atPC_executionEnv (s : State) (pc : Nat) (stack : List UInt256) :
    (atPC s pc stack).executionEnv = s.executionEnv := by rfl

@[simp] theorem atPC_memory (s : State) (pc : Nat) (stack : List UInt256) :
    (atPC s pc stack).memory = s.memory := by rfl

@[simp] theorem atPC_halt (s : State) (pc : Nat) (stack : List UInt256) :
    (atPC s pc stack).halt = s.halt := by rfl

@[simp] theorem returned_halt (s : State) (returnPC : Nat) (digest : UInt256) :
    (returned s returnPC digest).halt = .Returned := by rfl

@[simp] theorem returned_stack (s : State) (returnPC : Nat) (digest : UInt256) :
    (returned s returnPC digest).stack = [] := by rfl

@[simp] theorem returned_executionEnv (s : State) (returnPC : Nat) (digest : UInt256) :
    (returned s returnPC digest).executionEnv = s.executionEnv := by rfl

end Challenge.Ripemd160.Submission.H39Memo.DispatchState
