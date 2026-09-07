import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

def sizePath : List Located :=
  [opAt 5 .CALLDATASIZE, pushAt 6 2 1000,
   opAt 7 .XOR, pushAt 8 2 340, opAt 9 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 10 0 0, opAt 11 .CALLDATALOAD,
   opAt 12 (.Dup ⟨0, by decide⟩),
   pushAt 13 32 KnownInputData.fullWord, opAt 14 .XOR,
   pushAt 15 1 119, opAt 16 .JUMPI,
   pushAt 17 0 0, pushAt 18 1 32]

def checkEarlyPath : List Located :=
  [pushAt 10 0 0, opAt 11 .CALLDATALOAD,
   opAt 12 (.Dup ⟨0, by decide⟩),
   pushAt 13 32 KnownInputData.fullWord, opAt 14 .XOR,
   pushAt 15 1 119, opAt 16 .JUMPI,
   opAt 50 .JUMPDEST, opAt 51 .POP,
   pushAt 52 1 124, opAt 53 .JUMP]

def loopPath : List Located :=
  [opAt 19 .JUMPDEST, opAt 20 (.Swap ⟨0, by decide⟩),
   opAt 21 (.Dup ⟨1, by decide⟩), opAt 22 .CALLDATALOAD,
   opAt 23 (.Dup ⟨3, by decide⟩), opAt 24 .XOR, opAt 25 .OR,
   opAt 26 (.Swap ⟨0, by decide⟩), pushAt 27 1 32, opAt 28 .ADD,
   pushAt 29 2 992, opAt 30 (.Dup ⟨1, by decide⟩), opAt 31 .LT,
   pushAt 32 1 60, opAt 33 .JUMPI]

def tailPath : List Located :=
  [opAt 34 .CALLDATALOAD, opAt 35 (.Dup ⟨2, by decide⟩),
   opAt 36 .XOR, pushAt 37 1 192, opAt 38 .SHR, opAt 39 .OR,
   opAt 40 (.Swap ⟨0, by decide⟩), opAt 41 .POP,
   pushAt 42 2 340, opAt 43 .JUMPI]

def returnPath : List Located :=
  [pushAt 44 20 972889429405991776604892044862621566948497025487,
   pushAt 45 0 0, opAt 46 .MSTORE, pushAt 47 1 32,
   pushAt 48 0 0, opAt 49 .RETURN]

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-! The 6572-byte array stays opaque: only these projections of the initial
state are unfolded, so `simp` never normalizes it. -/

@[simp] theorem initialState_code (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.code = code := rfl

@[simp] theorem initialState_halt (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).halt = .Running := rfl

@[simp] theorem initialState_memory (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).memory = ByteArray.empty := rfl

@[simp] theorem initialState_activeWords (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).activeWords = 0 := rfl

attribute [simp] Challenge.Ripemd160.initialState_stack
  Challenge.Ripemd160.initialState_pc
  Challenge.Ripemd160.initialState_calldata

def sizeMatched (input : ByteArray) : State := atPC input 0x11
def fallbackState (input : ByteArray) : State := atPC input 0x154

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x3c
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x4f
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x5c

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x76
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 5 = 0x8 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 6 = 0x9 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 7 = 0xc := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 8 = 0xd := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 9 = 0x10 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 10 = 0x11 := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 11 = 0x12 := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 12 = 0x13 := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 13 = 0x14 := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 14 = 0x35 := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 15 = 0x36 := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 16 = 0x38 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 17 = 0x39 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 18 = 0x3a := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 19 = 0x3c := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 20 = 0x3d := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 21 = 0x3e := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 22 = 0x3f := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 23 = 0x40 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 24 = 0x41 := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 25 = 0x42 := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 26 = 0x43 := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 27 = 0x44 := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 28 = 0x46 := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 29 = 0x47 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 30 = 0x4a := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 31 = 0x4b := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 32 = 0x4c := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 33 = 0x4e := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 34 = 0x4f := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 35 = 0x50 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 36 = 0x51 := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 37 = 0x52 := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 38 = 0x54 := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 39 = 0x55 := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 40 = 0x56 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 41 = 0x57 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 42 = 0x58 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 43 = 0x5b := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 44 = 0x5c := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 45 = 0x71 := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 46 = 0x72 := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 47 = 0x73 := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 48 = 0x75 := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 49 = 0x76 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 50 = 0x77 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 51 = 0x78 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 52 = 0x79 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 53 = 0x7b := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
