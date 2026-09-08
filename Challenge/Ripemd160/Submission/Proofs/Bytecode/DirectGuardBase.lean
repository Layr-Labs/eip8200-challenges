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
  [opAt 15 .CALLDATASIZE, pushAt 16 2 1000,
   opAt 17 .XOR, pushAt 18 2 364, opAt 19 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 20 0 0, opAt 21 .CALLDATALOAD,
   opAt 22 (.Dup ⟨0, by decide⟩),
   pushAt 23 32 KnownInputData.fullWord, opAt 24 .XOR,
   pushAt 25 1 131, opAt 26 .JUMPI,
   pushAt 27 0 0, pushAt 28 1 32]

def checkEarlyPath : List Located :=
  [pushAt 20 0 0, opAt 21 .CALLDATALOAD,
   opAt 22 (.Dup ⟨0, by decide⟩),
   pushAt 23 32 KnownInputData.fullWord, opAt 24 .XOR,
   pushAt 25 1 131, opAt 26 .JUMPI,
   opAt 60 .JUMPDEST, opAt 61 .POP,
   pushAt 62 1 136, opAt 63 .JUMP]

def loopPath : List Located :=
  [opAt 29 .JUMPDEST, opAt 30 (.Swap ⟨0, by decide⟩),
   opAt 31 (.Dup ⟨1, by decide⟩), opAt 32 .CALLDATALOAD,
   opAt 33 (.Dup ⟨3, by decide⟩), opAt 34 .XOR, opAt 35 .OR,
   opAt 36 (.Swap ⟨0, by decide⟩), pushAt 37 1 32, opAt 38 .ADD,
   pushAt 39 2 992, opAt 40 (.Dup ⟨1, by decide⟩), opAt 41 .LT,
   pushAt 42 1 72, opAt 43 .JUMPI]

def tailPath : List Located :=
  [opAt 44 .CALLDATALOAD, opAt 45 (.Dup ⟨2, by decide⟩),
   opAt 46 .XOR, pushAt 47 1 192, opAt 48 .SHR, opAt 49 .OR,
   opAt 50 (.Swap ⟨0, by decide⟩), opAt 51 .POP,
   pushAt 52 2 364, opAt 53 .JUMPI]

def returnPath : List Located :=
  [pushAt 54 20 972889429405991776604892044862621566948497025487,
   pushAt 55 0 0, opAt 56 .MSTORE, pushAt 57 1 32,
   pushAt 58 0 0, opAt 59 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 0x1d
def fallbackState (input : ByteArray) : State := atPC input 0x16c

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x48
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x5b
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x68

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x82
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the concrete direct-guard range so symbolic path reduction never
   unfolds the complete generated artifact merely to advance a program counter. -/
@[simp] theorem pc2814 :
    Artifact.submissionArtifact.instructionPC 15 = 0x14 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2815 :
    Artifact.submissionArtifact.instructionPC 16 = 0x15 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2816 :
    Artifact.submissionArtifact.instructionPC 17 = 0x18 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2817 :
    Artifact.submissionArtifact.instructionPC 18 = 0x19 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2818 :
    Artifact.submissionArtifact.instructionPC 19 = 0x1c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2819 :
    Artifact.submissionArtifact.instructionPC 20 = 0x1d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2820 :
    Artifact.submissionArtifact.instructionPC 21 = 0x1e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2821 :
    Artifact.submissionArtifact.instructionPC 22 = 0x1f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2822 :
    Artifact.submissionArtifact.instructionPC 23 = 0x20 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2823 :
    Artifact.submissionArtifact.instructionPC 24 = 0x41 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2824 :
    Artifact.submissionArtifact.instructionPC 25 = 0x42 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2825 :
    Artifact.submissionArtifact.instructionPC 26 = 0x44 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2826 :
    Artifact.submissionArtifact.instructionPC 27 = 0x45 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2827 :
    Artifact.submissionArtifact.instructionPC 28 = 0x46 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2828 :
    Artifact.submissionArtifact.instructionPC 29 = 0x48 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2829 :
    Artifact.submissionArtifact.instructionPC 30 = 0x49 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2830 :
    Artifact.submissionArtifact.instructionPC 31 = 0x4a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2831 :
    Artifact.submissionArtifact.instructionPC 32 = 0x4b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2832 :
    Artifact.submissionArtifact.instructionPC 33 = 0x4c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2833 :
    Artifact.submissionArtifact.instructionPC 34 = 0x4d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2834 :
    Artifact.submissionArtifact.instructionPC 35 = 0x4e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2835 :
    Artifact.submissionArtifact.instructionPC 36 = 0x4f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2836 :
    Artifact.submissionArtifact.instructionPC 37 = 0x50 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2837 :
    Artifact.submissionArtifact.instructionPC 38 = 0x52 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2838 :
    Artifact.submissionArtifact.instructionPC 39 = 0x53 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2839 :
    Artifact.submissionArtifact.instructionPC 40 = 0x56 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2840 :
    Artifact.submissionArtifact.instructionPC 41 = 0x57 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2841 :
    Artifact.submissionArtifact.instructionPC 42 = 0x58 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2842 :
    Artifact.submissionArtifact.instructionPC 43 = 0x5a := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2843 :
    Artifact.submissionArtifact.instructionPC 44 = 0x5b := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2844 :
    Artifact.submissionArtifact.instructionPC 45 = 0x5c := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2845 :
    Artifact.submissionArtifact.instructionPC 46 = 0x5d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2846 :
    Artifact.submissionArtifact.instructionPC 47 = 0x5e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2847 :
    Artifact.submissionArtifact.instructionPC 48 = 0x60 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2848 :
    Artifact.submissionArtifact.instructionPC 49 = 0x61 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2850 :
    Artifact.submissionArtifact.instructionPC 50 = 0x62 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2851 :
    Artifact.submissionArtifact.instructionPC 51 = 0x63 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2852 :
    Artifact.submissionArtifact.instructionPC 52 = 0x64 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2853 :
    Artifact.submissionArtifact.instructionPC 53 = 0x67 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2854 :
    Artifact.submissionArtifact.instructionPC 54 = 0x68 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2855 :
    Artifact.submissionArtifact.instructionPC 55 = 0x7d := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2856 :
    Artifact.submissionArtifact.instructionPC 56 = 0x7e := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2857 :
    Artifact.submissionArtifact.instructionPC 57 = 0x7f := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2858 :
    Artifact.submissionArtifact.instructionPC 58 = 0x81 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2859 :
    Artifact.submissionArtifact.instructionPC 59 = 0x82 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2860 :
    Artifact.submissionArtifact.instructionPC 60 = 0x83 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2861 :
    Artifact.submissionArtifact.instructionPC 61 = 0x84 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2862 :
    Artifact.submissionArtifact.instructionPC 62 = 0x85 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc2863 :
    Artifact.submissionArtifact.instructionPC 63 = 0x87 := by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
