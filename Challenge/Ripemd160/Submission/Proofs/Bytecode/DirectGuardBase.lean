import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardGrouping
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail

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

/-- Entry byte gate: `byte0 == 7` jumps to the patterned guard at 4827. -/
def bytePrefix : List Located :=
  [pushAt 6 1 7,
   pushAt 7 0 0,
   opAt 8 .CALLDATALOAD,
   pushAt 9 0 0,
   opAt 10 .BYTE,
   opAt 11 .EQ,
   pushAt 12 2 4681]

/-- Entry size guard: sizes below four jump to the patterned guard at 4681. -/
def guardPrefix : List Located :=
  [pushAt 14 1 4,
   opAt 15 .CALLDATASIZE,
   opAt 16 .LT,
   pushAt 17 2 4681]

/-- Exact size gate: `1000 - size != 0` jumps to the generic arm. -/
def sizePrefix : List Located :=
  [opAt 19 .CALLDATASIZE,
   pushAt 20 2 1000,
   opAt 21 .SUB,
   pushAt 22 1 246]

def entryDest : Located := opAt 147 .JUMPDEST

/-- The reference word, the anchor test `R * 255 + 97` and the tail word fold
into the seed accumulator. -/
def checkEntryPath : List Located :=
  [pushAt 24 0 0,
   opAt 25 .CALLDATALOAD,
   pushAt 26 2 960,
   pushAt 27 1 97,
   pushAt 28 1 255,
   opAt 29 (.Dup ⟨3, by decide⟩),
   opAt 30 .MUL,
   opAt 31 .ADD,
   pushAt 32 2 968,
   opAt 33 .CALLDATALOAD,
   opAt 34 (.Dup ⟨3, by decide⟩),
   opAt 35 .XOR,
   opAt 36 .OR]

def loopPath : List Located :=
  [opAt 37 .JUMPDEST,
   pushAt 38 1 32,
   opAt 39 (.Dup ⟨2, by decide⟩),
   opAt 40 .SUB,
   opAt 41 .CALLDATALOAD,
   opAt 42 (.Dup ⟨3, by decide⟩),
   opAt 43 .XOR,
   opAt 44 .OR,
   pushAt 45 1 64,
   opAt 46 (.Dup ⟨2, by decide⟩),
   opAt 47 .SUB,
   opAt 48 (.Swap ⟨1, by decide⟩),
   opAt 49 .CALLDATALOAD,
   opAt 50 (.Dup ⟨3, by decide⟩),
   opAt 51 .XOR,
   opAt 52 .OR,
   opAt 53 (.Dup ⟨1, by decide⟩),
   pushAt 54 1 58,
   opAt 55 .JUMPI]

/-- Branch on the accumulator directly. The generic implementation carries the
zero counter and anchor below it as a suffix. -/
def tailPath : List Located :=
  [pushAt 56 1 246,
   opAt 57 .JUMPI]

/-- Off the measured path: the divert lands on the generic arm's entry. -/
def fallbackPath : List Located :=
  [entryDest]

def returnPath : List Located :=
  [pushAt 58 20 972889429405991776604892044862621566948497025487,
   pushAt 59 0 0,
   opAt 60 .MSTORE]

def returnFinishPath : List Located :=
  [pushAt 62 0 0,
   opAt 63 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 39

def spentCells (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat 0, referenceWord input]

def fallbackState (input : ByteArray) : State :=
  StackTail.append (atPC input 247) (spentCells input)

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 58
    stack := [reverseAcc input n, UInt256.ofNat (960 - 64 * n), referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 80
    stack := [reverseAcc input 15, UInt256.ofNat 0, referenceWord input] }

def returnEntry (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 83
    stack := spentCells input }

def tailDivertState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 246
    stack := spentCells input }

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 108
    stack := spentCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storedReturnState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 106
    stack := spentCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedReturnState (input : ByteArray) : State :=
  { storedReturnState input with
    pc := UInt256.ofNat 107
    stack := UInt256.ofNat 32 :: spentCells input }

abbrev run := Challenge.EvmProof.DataStepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the exact concrete instruction PCs used by the guard. -/
@[simp] theorem pc_direct_6 : Artifact.submissionArtifact.instructionPC 6 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_7 : Artifact.submissionArtifact.instructionPC 7 = 14 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_8 : Artifact.submissionArtifact.instructionPC 8 = 15 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_9 : Artifact.submissionArtifact.instructionPC 9 = 16 := by
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
@[simp] theorem pc_direct_15 : Artifact.submissionArtifact.instructionPC 15 = 25 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_16 : Artifact.submissionArtifact.instructionPC 16 = 26 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_17 : Artifact.submissionArtifact.instructionPC 17 = 27 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_18 : Artifact.submissionArtifact.instructionPC 18 = 30 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_19 : Artifact.submissionArtifact.instructionPC 19 = 31 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_20 : Artifact.submissionArtifact.instructionPC 20 = 32 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_21 : Artifact.submissionArtifact.instructionPC 21 = 35 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_22 : Artifact.submissionArtifact.instructionPC 22 = 36 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_23 : Artifact.submissionArtifact.instructionPC 23 = 38 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_24 : Artifact.submissionArtifact.instructionPC 24 = 39 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_25 : Artifact.submissionArtifact.instructionPC 25 = 40 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_26 : Artifact.submissionArtifact.instructionPC 26 = 41 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_27 : Artifact.submissionArtifact.instructionPC 27 = 44 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_28 : Artifact.submissionArtifact.instructionPC 28 = 46 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_29 : Artifact.submissionArtifact.instructionPC 29 = 48 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_30 : Artifact.submissionArtifact.instructionPC 30 = 49 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_31 : Artifact.submissionArtifact.instructionPC 31 = 50 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_32 : Artifact.submissionArtifact.instructionPC 32 = 51 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_33 : Artifact.submissionArtifact.instructionPC 33 = 54 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_34 : Artifact.submissionArtifact.instructionPC 34 = 55 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_35 : Artifact.submissionArtifact.instructionPC 35 = 56 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_36 : Artifact.submissionArtifact.instructionPC 36 = 57 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_37 : Artifact.submissionArtifact.instructionPC 37 = 58 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_38 : Artifact.submissionArtifact.instructionPC 38 = 59 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_39 : Artifact.submissionArtifact.instructionPC 39 = 61 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_40 : Artifact.submissionArtifact.instructionPC 40 = 62 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_41 : Artifact.submissionArtifact.instructionPC 41 = 63 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_42 : Artifact.submissionArtifact.instructionPC 42 = 64 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_43 : Artifact.submissionArtifact.instructionPC 43 = 65 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_44 : Artifact.submissionArtifact.instructionPC 44 = 66 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_45 : Artifact.submissionArtifact.instructionPC 45 = 67 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_46 : Artifact.submissionArtifact.instructionPC 46 = 69 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_47 : Artifact.submissionArtifact.instructionPC 47 = 70 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_48 : Artifact.submissionArtifact.instructionPC 48 = 71 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_49 : Artifact.submissionArtifact.instructionPC 49 = 72 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_50 : Artifact.submissionArtifact.instructionPC 50 = 73 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_51 : Artifact.submissionArtifact.instructionPC 51 = 74 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_52 : Artifact.submissionArtifact.instructionPC 52 = 75 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_53 : Artifact.submissionArtifact.instructionPC 53 = 76 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_54 : Artifact.submissionArtifact.instructionPC 54 = 77 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_55 : Artifact.submissionArtifact.instructionPC 55 = 79 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_56 : Artifact.submissionArtifact.instructionPC 56 = 80 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_57 : Artifact.submissionArtifact.instructionPC 57 = 82 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_58 : Artifact.submissionArtifact.instructionPC 58 = 83 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_59 : Artifact.submissionArtifact.instructionPC 59 = 104 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_60 : Artifact.submissionArtifact.instructionPC 60 = 105 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_61 : Artifact.submissionArtifact.instructionPC 61 = 106 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_62 : Artifact.submissionArtifact.instructionPC 62 = 107 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_63 : Artifact.submissionArtifact.instructionPC 63 = 108 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_64 : Artifact.submissionArtifact.instructionPC 64 = 109 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_65 : Artifact.submissionArtifact.instructionPC 65 = 110 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_66 : Artifact.submissionArtifact.instructionPC 66 = 111 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_67 : Artifact.submissionArtifact.instructionPC 67 = 112 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_68 : Artifact.submissionArtifact.instructionPC 68 = 113 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_69 : Artifact.submissionArtifact.instructionPC 69 = 114 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_70 : Artifact.submissionArtifact.instructionPC 70 = 115 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_71 : Artifact.submissionArtifact.instructionPC 71 = 116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_72 : Artifact.submissionArtifact.instructionPC 72 = 118 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_73 : Artifact.submissionArtifact.instructionPC 73 = 120 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_74 : Artifact.submissionArtifact.instructionPC 74 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
