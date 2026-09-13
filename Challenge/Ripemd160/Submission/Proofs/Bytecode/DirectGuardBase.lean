import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardGrouping

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState
@[simp] private theorem literalZeroWord : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := rfl
@[simp] private theorem zeroWordNat : (0 : UInt256).toNat = 0 := rfl

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.DataStepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.DataStepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

def sizePath : List Located :=
  [opAt 5 .CALLDATASIZE,
   pushAt 6 2 256,
   opAt 7 .EQ,
   opAt 8 .CALLDATASIZE,
   pushAt 9 2 376,
   opAt 10 .EQ,
   opAt 11 .CALLDATASIZE,
   pushAt 12 2 1000,
   opAt 13 .EQ,
   opAt 14 .OR,
   opAt 15 .OR,
   opAt 16 .ISZERO,
   pushAt 17 2 4859,
   opAt 18 .JUMPI]

def checkEntryPath : List Located :=
  [pushAt 19 1 97,
   pushAt 20 1 255,
   pushAt 21 0 0,
   opAt 22 .NOT,
   opAt 23 .DIV,
   opAt 24 .MUL,
   pushAt 25 0 0,
   opAt 26 .CALLDATALOAD,
   opAt 27 .XOR,
   pushAt 28 1 115,
   opAt 29 .JUMPI,
   pushAt 30 0 0,
   opAt 31 .CALLDATALOAD,
   opAt 32 (.Dup ⟨0, by decide⟩),
   pushAt 33 2 992,
   opAt 34 .CALLDATALOAD,
   opAt 35 .XOR,
   pushAt 36 1 192,
   opAt 37 .SHR,
   pushAt 38 2 960]

def checkEarlyPath : List Located :=
  [pushAt 19 1 97,
   pushAt 20 1 255,
   pushAt 21 0 0,
   opAt 22 .NOT,
   opAt 23 .DIV,
   opAt 24 .MUL,
   pushAt 25 0 0,
   opAt 26 .CALLDATALOAD,
   opAt 27 .XOR,
   pushAt 28 1 115,
   opAt 29 .JUMPI,
   opAt 71 .JUMPDEST]

def loopPath : List Located :=
  [opAt 39 .JUMPDEST,
   opAt 40 (.Swap ⟨0, by decide⟩),
   opAt 41 (.Dup ⟨2, by decide⟩),
   opAt 42 (.Dup ⟨2, by decide⟩),
   opAt 43 .CALLDATALOAD,
   opAt 44 .XOR,
   opAt 45 .OR,
   pushAt 46 1 32,
   opAt 47 (.Dup ⟨2, by decide⟩),
   opAt 48 .SUB,
   opAt 49 .CALLDATALOAD,
   opAt 50 (.Dup ⟨3, by decide⟩),
   opAt 51 .XOR,
   opAt 52 .OR,
   opAt 53 (.Swap ⟨0, by decide⟩),
   pushAt 54 1 64,
   opAt 55 (.Swap ⟨0, by decide⟩),
   opAt 56 .SUB,
   opAt 57 (.Dup ⟨0, by decide⟩),
   pushAt 58 1 58,
   opAt 59 .JUMPI]

def tailPath : List Located :=
  [opAt 60 .POP,
   opAt 61 (.Swap ⟨0, by decide⟩),
   opAt 62 .POP,
   pushAt 63 2 358,
   opAt 64 .JUMPI]

def returnPath : List Located :=
  [pushAt 65 20 972889429405991776604892044862621566948497025487,
   pushAt 66 0 0,
   opAt 67 .MSTORE]

def returnFinishPath : List Located :=
  [pushAt 69 0 0,
   opAt 70 .RETURN]

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-! The concrete byte array stays opaque: only these projections of the initial
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

def sizeMatched (input : ByteArray) : State := atPC input 30
def fallbackState (input : ByteArray) : State := atPC input 358

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 58
    stack := [UInt256.ofNat (960 - 64 * n), reverseAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 82
    stack := [UInt256.ofNat 0, finalAcc input, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 89

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 114
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storedReturnState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 112
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedReturnState (input : ByteArray) : State :=
  { storedReturnState input with
    pc := UInt256.ofNat 113
    stack := [UInt256.ofNat 32] }

abbrev run := Challenge.EvmProof.DataStepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the exact concrete instruction PCs used by the guard. -/
@[simp] theorem pc_direct_0 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_1 : Artifact.submissionArtifact.instructionPC 1 = 1 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_2 : Artifact.submissionArtifact.instructionPC 2 = 3 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_3 : Artifact.submissionArtifact.instructionPC 3 = 4 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_4 : Artifact.submissionArtifact.instructionPC 4 = 7 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_5 : Artifact.submissionArtifact.instructionPC 5 = 8 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_6 : Artifact.submissionArtifact.instructionPC 6 = 9 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_7 : Artifact.submissionArtifact.instructionPC 7 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_8 : Artifact.submissionArtifact.instructionPC 8 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_9 : Artifact.submissionArtifact.instructionPC 9 = 14 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_10 : Artifact.submissionArtifact.instructionPC 10 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_11 : Artifact.submissionArtifact.instructionPC 11 = 18 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_12 : Artifact.submissionArtifact.instructionPC 12 = 19 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_13 : Artifact.submissionArtifact.instructionPC 13 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_14 : Artifact.submissionArtifact.instructionPC 14 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_15 : Artifact.submissionArtifact.instructionPC 15 = 24 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_16 : Artifact.submissionArtifact.instructionPC 16 = 25 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_17 : Artifact.submissionArtifact.instructionPC 17 = 26 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_18 : Artifact.submissionArtifact.instructionPC 18 = 29 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_19 : Artifact.submissionArtifact.instructionPC 19 = 30 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_20 : Artifact.submissionArtifact.instructionPC 20 = 32 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_21 : Artifact.submissionArtifact.instructionPC 21 = 34 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_22 : Artifact.submissionArtifact.instructionPC 22 = 35 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_23 : Artifact.submissionArtifact.instructionPC 23 = 36 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_24 : Artifact.submissionArtifact.instructionPC 24 = 37 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_25 : Artifact.submissionArtifact.instructionPC 25 = 38 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_26 : Artifact.submissionArtifact.instructionPC 26 = 39 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_27 : Artifact.submissionArtifact.instructionPC 27 = 40 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_28 : Artifact.submissionArtifact.instructionPC 28 = 41 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_29 : Artifact.submissionArtifact.instructionPC 29 = 43 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_30 : Artifact.submissionArtifact.instructionPC 30 = 44 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_31 : Artifact.submissionArtifact.instructionPC 31 = 45 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_32 : Artifact.submissionArtifact.instructionPC 32 = 46 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_33 : Artifact.submissionArtifact.instructionPC 33 = 47 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_34 : Artifact.submissionArtifact.instructionPC 34 = 50 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_35 : Artifact.submissionArtifact.instructionPC 35 = 51 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_36 : Artifact.submissionArtifact.instructionPC 36 = 52 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_37 : Artifact.submissionArtifact.instructionPC 37 = 54 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_38 : Artifact.submissionArtifact.instructionPC 38 = 55 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_39 : Artifact.submissionArtifact.instructionPC 39 = 58 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_40 : Artifact.submissionArtifact.instructionPC 40 = 59 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_41 : Artifact.submissionArtifact.instructionPC 41 = 60 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_42 : Artifact.submissionArtifact.instructionPC 42 = 61 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_43 : Artifact.submissionArtifact.instructionPC 43 = 62 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_44 : Artifact.submissionArtifact.instructionPC 44 = 63 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_45 : Artifact.submissionArtifact.instructionPC 45 = 64 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_46 : Artifact.submissionArtifact.instructionPC 46 = 65 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_47 : Artifact.submissionArtifact.instructionPC 47 = 67 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_48 : Artifact.submissionArtifact.instructionPC 48 = 68 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_49 : Artifact.submissionArtifact.instructionPC 49 = 69 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_50 : Artifact.submissionArtifact.instructionPC 50 = 70 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_51 : Artifact.submissionArtifact.instructionPC 51 = 71 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_52 : Artifact.submissionArtifact.instructionPC 52 = 72 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_53 : Artifact.submissionArtifact.instructionPC 53 = 73 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_54 : Artifact.submissionArtifact.instructionPC 54 = 74 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_55 : Artifact.submissionArtifact.instructionPC 55 = 76 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_56 : Artifact.submissionArtifact.instructionPC 56 = 77 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_57 : Artifact.submissionArtifact.instructionPC 57 = 78 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_58 : Artifact.submissionArtifact.instructionPC 58 = 79 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_59 : Artifact.submissionArtifact.instructionPC 59 = 81 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_60 : Artifact.submissionArtifact.instructionPC 60 = 82 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_61 : Artifact.submissionArtifact.instructionPC 61 = 83 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_62 : Artifact.submissionArtifact.instructionPC 62 = 84 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_63 : Artifact.submissionArtifact.instructionPC 63 = 85 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_64 : Artifact.submissionArtifact.instructionPC 64 = 88 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_65 : Artifact.submissionArtifact.instructionPC 65 = 89 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_66 : Artifact.submissionArtifact.instructionPC 66 = 110 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_67 : Artifact.submissionArtifact.instructionPC 67 = 111 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_68 : Artifact.submissionArtifact.instructionPC 68 = 112 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_69 : Artifact.submissionArtifact.instructionPC 69 = 113 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_70 : Artifact.submissionArtifact.instructionPC 70 = 114 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_71 : Artifact.submissionArtifact.instructionPC 71 = 115 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_72 : Artifact.submissionArtifact.instructionPC 72 = 116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem producerEndPC : Artifact.submissionArtifact.instructionPC 25 = 38 := pc_direct_25
@[simp] theorem earlyWordLoadPC : Artifact.submissionArtifact.instructionPC 26 = 39 := pc_direct_26
@[simp] theorem pc2823 : Artifact.submissionArtifact.instructionPC 27 = 40 := pc_direct_27
@[simp] theorem pc2824 : Artifact.submissionArtifact.instructionPC 28 = 41 := pc_direct_28
@[simp] theorem pc2825 : Artifact.submissionArtifact.instructionPC 29 = 43 := pc_direct_29
@[simp] theorem pc2860 : Artifact.submissionArtifact.instructionPC 71 = 115 := pc_direct_71
@[simp] theorem pc_classifier_112 : Artifact.submissionArtifact.instructionPC 17 = 26 := pc_direct_17
@[simp] theorem pc_classifier_113 : Artifact.submissionArtifact.instructionPC 18 = 29 := pc_direct_18

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
