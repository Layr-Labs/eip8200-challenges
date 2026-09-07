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
  [opAt 0 .JUMPDEST, opAt 1 .CALLDATASIZE, pushAt 2 2 1000,
   opAt 3 .XOR, pushAt 4 2 330, opAt 5 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 6 0 0, opAt 7 .CALLDATALOAD,
   opAt 8 (.Dup ⟨0, by decide⟩),
   pushAt 9 32 KnownInputData.fullWord, opAt 10 .XOR,
   pushAt 11 1 113, opAt 12 .JUMPI,
   pushAt 13 0 0, pushAt 14 1 32]

def checkEarlyPath : List Located :=
  [pushAt 6 0 0, opAt 7 .CALLDATALOAD,
   opAt 8 (.Dup ⟨0, by decide⟩),
   pushAt 9 32 KnownInputData.fullWord, opAt 10 .XOR,
   pushAt 11 1 113, opAt 12 .JUMPI,
   opAt 47 .JUMPDEST, opAt 48 .POP,
   pushAt 49 1 118, opAt 50 .JUMP]

def loopPath : List Located :=
  [opAt 15 .JUMPDEST, opAt 16 (.Swap ⟨0, by decide⟩),
   opAt 17 (.Dup ⟨1, by decide⟩), opAt 18 .CALLDATALOAD,
   opAt 19 (.Dup ⟨3, by decide⟩), opAt 20 .XOR, opAt 21 .OR,
   opAt 22 (.Swap ⟨0, by decide⟩), pushAt 23 1 32, opAt 24 .ADD,
   pushAt 25 2 992, opAt 26 (.Dup ⟨1, by decide⟩), opAt 27 .LT,
   pushAt 28 1 53, opAt 29 .JUMPI]

def tailPath : List Located :=
  [opAt 30 .CALLDATALOAD, opAt 31 (.Dup ⟨2, by decide⟩),
   opAt 32 .XOR, pushAt 33 1 192, opAt 34 .SHR, opAt 35 .OR,
   opAt 36 .JUMPDEST, opAt 37 (.Swap ⟨0, by decide⟩), opAt 38 .POP,
   pushAt 39 2 330, opAt 40 .JUMPI]

def returnPath : List Located :=
  [pushAt 41 20 972889429405991776604892044862621566948497025487,
   pushAt 42 0 0, opAt 43 .MSTORE, pushAt 44 1 32,
   pushAt 45 0 0, opAt 46 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0xa
def fallbackState (input : ByteArray) : State := atPC input 0x14a

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x35
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x48
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x56

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x70
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 0 = 0x0 := by rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 1 = 0x1 := by rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 2 = 0x2 := by rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 3 = 0x5 := by rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 4 = 0x6 := by rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 5 = 0x9 := by rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 6 = 0xa := by rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 7 = 0xb := by rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 8 = 0xc := by rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 9 = 0xd := by rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 10 = 0x2e := by rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 11 = 0x2f := by rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 12 = 0x31 := by rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 13 = 0x32 := by rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 14 = 0x33 := by rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 15 = 0x35 := by rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 16 = 0x36 := by rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 17 = 0x37 := by rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 18 = 0x38 := by rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 19 = 0x39 := by rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 20 = 0x3a := by rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 21 = 0x3b := by rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 22 = 0x3c := by rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 23 = 0x3d := by rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 24 = 0x3f := by rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 25 = 0x40 := by rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 26 = 0x43 := by rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 27 = 0x44 := by rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 28 = 0x45 := by rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 29 = 0x47 := by rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 30 = 0x48 := by rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 31 = 0x49 := by rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 32 = 0x4a := by rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 33 = 0x4b := by rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 34 = 0x4d := by rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 35 = 0x4e := by rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 36 = 0x4f := by rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 37 = 0x50 := by rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 38 = 0x51 := by rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 39 = 0x52 := by rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 40 = 0x55 := by rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 41 = 0x56 := by rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 42 = 0x6b := by rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 43 = 0x6c := by rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 44 = 0x6d := by rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 45 = 0x6f := by rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 46 = 0x70 := by rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 47 = 0x71 := by rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 48 = 0x72 := by rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 49 = 0x73 := by rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 50 = 0x75 := by rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
