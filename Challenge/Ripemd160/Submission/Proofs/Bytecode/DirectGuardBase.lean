import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
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
  [opAt 0 .CALLDATASIZE,
   pushAt 1 3 256,
   opAt 2 .EQ,
   opAt 3 .CALLDATASIZE,
   pushAt 4 3 376,
   opAt 5 .EQ,
   opAt 6 .CALLDATASIZE,
   pushAt 7 2 1000,
   opAt 8 .EQ,
   opAt 9 .OR,
   opAt 10 .OR,
   opAt 11 .ISZERO,
   pushAt 12 2 5129,
   opAt 13 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 14 0 0, opAt 15 .CALLDATALOAD,
   opAt 16 (.Dup ⟨0, by decide⟩),
   pushAt 17 1 255, pushAt 18 0 0, opAt 19 .NOT, opAt 20 .DIV,
   pushAt 21 1 97, opAt 22 .MUL, opAt 23 .XOR,
   pushAt 24 1 101, opAt 25 .JUMPI,
   pushAt 26 0 0, pushAt 27 1 32]

def checkEarlyPath : List Located :=
  [pushAt 14 0 0, opAt 15 .CALLDATALOAD,
   opAt 16 (.Dup ⟨0, by decide⟩),
   pushAt 17 1 255, pushAt 18 0 0, opAt 19 .NOT, opAt 20 .DIV,
   pushAt 21 1 97, opAt 22 .MUL, opAt 23 .XOR,
   pushAt 24 1 101, opAt 25 .JUMPI,
   opAt 59 .JUMPDEST, opAt 60 .POP]

def loopPath : List Located :=
  [opAt 28 .JUMPDEST, opAt 29 (.Swap ⟨0, by decide⟩),
   opAt 30 (.Dup ⟨1, by decide⟩), opAt 31 .CALLDATALOAD,
   opAt 32 (.Dup ⟨3, by decide⟩), opAt 33 .XOR, opAt 34 .OR,
   opAt 35 (.Swap ⟨0, by decide⟩), pushAt 36 1 32, opAt 37 .ADD,
   pushAt 38 2 992, opAt 39 (.Dup ⟨1, by decide⟩), opAt 40 .LT,
   pushAt 41 1 42, opAt 42 .JUMPI]

def tailPath : List Located :=
  [opAt 43 .CALLDATALOAD, opAt 44 (.Dup ⟨2, by decide⟩),
   opAt 45 .XOR, pushAt 46 1 192, opAt 47 .SHR, opAt 48 .OR,
   opAt 49 (.Swap ⟨0, by decide⟩), opAt 50 .POP,
   pushAt 51 2 369, opAt 52 .JUMPI]

def returnPath : List Located :=
  [pushAt 53 21 972889429405991776604892044862621566948497025487,
   pushAt 54 0 0, opAt 55 .MSTORE]

def returnFinishPath : List Located :=
  [pushAt 57 0 0, opAt 58 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x18
def fallbackState (input : ByteArray) : State := atPC input 0x171

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x2a
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x3d
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x4a

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x64
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storedReturnState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 98
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedReturnState (input : ByteArray) : State :=
  { storedReturnState input with
    pc := UInt256.ofNat 99
    stack := [UInt256.ofNat 32] }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc_cls98 :
    Artifact.submissionArtifact.instructionPC 0 = 0x0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls99 :
    Artifact.submissionArtifact.instructionPC 4 = 0x7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls101 :
    Artifact.submissionArtifact.instructionPC 0 = 0x0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls103 :
    Artifact.submissionArtifact.instructionPC 4 = 0x7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls104 :
    Artifact.submissionArtifact.instructionPC 4 = 0x7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls105 :
    Artifact.submissionArtifact.instructionPC 5 = 0xb := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls106 :
    Artifact.submissionArtifact.instructionPC 6 = 0xc := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls108 :
    Artifact.submissionArtifact.instructionPC 8 = 0x10 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls109 :
    Artifact.submissionArtifact.instructionPC 9 = 0x11 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_cls110 :
    Artifact.submissionArtifact.instructionPC 11 = 0x13 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2813 :
    Artifact.submissionArtifact.instructionPC 0 = 0x0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 0 = 0x0 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 7 = 0xd := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 4 = 0x7 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 12 = 0x14 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 13 = 0x17 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 14 = 0x18 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 15 = 0x19 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 16 = 0x1a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 17 = 0x1b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 23 = 0x23 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 24 = 0x24 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 25 = 0x26 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 26 = 0x27 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 27 = 0x28 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 28 = 0x2a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 29 = 0x2b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 30 = 0x2c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 31 = 0x2d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 32 = 0x2e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 33 = 0x2f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 34 = 0x30 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 35 = 0x31 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 36 = 0x32 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 37 = 0x34 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 38 = 0x35 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 39 = 0x38 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 40 = 0x39 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 41 = 0x3a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 42 = 0x3c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 43 = 0x3d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 44 = 0x3e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 45 = 0x3f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 46 = 0x40 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 47 = 0x42 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 48 = 0x43 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2849 :
    Artifact.submissionArtifact.instructionPC 49 = 0x44 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 49 = 0x44 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 50 = 0x45 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 51 = 0x46 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 52 = 0x49 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 53 = 0x4a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 54 = 0x60 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 55 = 0x61 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 56 = 0x62 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 57 = 0x63 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 58 = 0x64 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 59 = 0x65 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 60 = 0x66 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 61 = 0x67 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 61 = 0x67 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem pc_classifier_97 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_98 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_99 : Artifact.submissionArtifact.instructionPC 1 = 1 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_100 : Artifact.submissionArtifact.instructionPC 1 = 1 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_101 : Artifact.submissionArtifact.instructionPC 2 = 5 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_102 : Artifact.submissionArtifact.instructionPC 3 = 6 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_103 : Artifact.submissionArtifact.instructionPC 4 = 7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_104 : Artifact.submissionArtifact.instructionPC 4 = 7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_105 : Artifact.submissionArtifact.instructionPC 5 = 11 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_106 : Artifact.submissionArtifact.instructionPC 6 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_107 : Artifact.submissionArtifact.instructionPC 7 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_108 : Artifact.submissionArtifact.instructionPC 8 = 16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_109 : Artifact.submissionArtifact.instructionPC 9 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_110 : Artifact.submissionArtifact.instructionPC 10 = 18 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_111 : Artifact.submissionArtifact.instructionPC 11 = 19 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_112 : Artifact.submissionArtifact.instructionPC 12 = 20 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_classifier_113 : Artifact.submissionArtifact.instructionPC 13 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
