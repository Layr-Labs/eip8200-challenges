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

/-- Entry byte gate: `byte0 == 7` jumps to the patterned guard at 4827. -/
def bytePrefix : List Located :=
  [pushAt 6 1 7,
   pushAt 7 0 0,
   opAt 8 .CALLDATALOAD,
   pushAt 9 0 0,
   opAt 10 .BYTE,
   opAt 11 .EQ,
   pushAt 12 2 4819]

/-- Entry size gate: `(size >> 2) * (size ^ 1000) != 0` jumps to the generic arm. -/
def gatePrefix : List Located :=
  [pushAt 14 2 1000,
   opAt 15 .CALLDATASIZE,
   opAt 16 .XOR,
   opAt 17 .CALLDATASIZE,
   pushAt 18 1 2,
   opAt 19 .SHR,
   opAt 20 .MUL,
   pushAt 21 2 343]

def checkEntryPath : List Located :=
  [pushAt 23 0 0,
   opAt 24 .CALLDATALOAD,
   pushAt 25 1 97,
   pushAt 26 1 255,
   pushAt 27 0 0,
   opAt 28 .NOT,
   opAt 29 .DIV,
   opAt 30 .MUL,
   opAt 31 .XOR,
   pushAt 32 2 4819,
   opAt 33 .JUMPI,
   pushAt 34 0 0,
   opAt 35 .CALLDATALOAD,
   pushAt 36 2 960,
   pushAt 37 2 968,
   opAt 38 .CALLDATALOAD,
   opAt 39 (.Dup ⟨2, by decide⟩),
   opAt 40 .XOR]

def loopPath : List Located :=
  [opAt 41 .JUMPDEST,
   pushAt 42 1 32,
   opAt 43 (.Dup ⟨2, by decide⟩),
   opAt 44 .SUB,
   opAt 45 .CALLDATALOAD,
   opAt 46 (.Dup ⟨3, by decide⟩),
   opAt 47 .XOR,
   opAt 48 .OR,
   pushAt 49 1 64,
   opAt 50 (.Dup ⟨2, by decide⟩),
   opAt 51 .SUB,
   opAt 52 (.Swap ⟨1, by decide⟩),
   opAt 53 .CALLDATALOAD,
   opAt 54 (.Dup ⟨3, by decide⟩),
   opAt 55 .XOR,
   opAt 56 .OR,
   opAt 57 (.Dup ⟨1, by decide⟩),
   pushAt 58 1 64,
   opAt 59 .JUMPI]

/-- The exit test now consumes the accumulator itself: a nonzero accumulator
jumps to the clearing stub at 105, a zero accumulator falls straight into the
digest store with the spent counter and the anchor still on the stack. -/
def tailPath : List Located :=
  [pushAt 60 1 115,
   opAt 61 .JUMPI]

/-- Off the measured path: drop the two spent cells and enter the generic arm. -/
def fallbackPath : List Located :=
  [opAt 68 .JUMPDEST,
   opAt 69 .POP,
   pushAt 70 2 343,
   opAt 71 .JUMPI]

def returnPath : List Located :=
  [pushAt 62 20 972889429405991776604892044862621566948497025487,
   pushAt 63 0 0,
   opAt 64 .MSTORE]

def returnFinishPath : List Located :=
  [pushAt 66 0 0,
   opAt 67 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 38
def fallbackState (input : ByteArray) : State := atPC input 343

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 64
    stack := [reverseAcc input n, UInt256.ofNat (960 - 64 * n), referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 86
    stack := [finalAcc input, UInt256.ofNat 0, referenceWord input] }

/-- The two cells the exit test leaves behind: the spent counter and the anchor
word.  `RETURN` reads memory only, so the digest store runs on top of them. -/
def spentCells (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat 0, referenceWord input]

def returnEntry (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 89
    stack := spentCells input }

def tailDivertState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 115
    stack := spentCells input }

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 114
    stack := spentCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storedReturnState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 112
    stack := spentCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedReturnState (input : ByteArray) : State :=
  { storedReturnState input with
    pc := UInt256.ofNat 113
    stack := UInt256.ofNat 32 :: spentCells input }

abbrev run := Challenge.EvmProof.DataStepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the exact concrete instruction PCs used by the guard. -/
@[simp] theorem pc_direct_0 : Artifact.submissionArtifact.instructionPC 6 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_1 : Artifact.submissionArtifact.instructionPC 7 = 15 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_2 : Artifact.submissionArtifact.instructionPC 8 = 16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_3 : Artifact.submissionArtifact.instructionPC 9 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_4 : Artifact.submissionArtifact.instructionPC 10 = 18 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_5 : Artifact.submissionArtifact.instructionPC 11 = 19 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_6 : Artifact.submissionArtifact.instructionPC 12 = 20 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_7 : Artifact.submissionArtifact.instructionPC 13 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_8 : Artifact.submissionArtifact.instructionPC 14 = 24 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_9 : Artifact.submissionArtifact.instructionPC 15 = 27 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_10 : Artifact.submissionArtifact.instructionPC 16 = 28 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_11 : Artifact.submissionArtifact.instructionPC 17 = 29 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_12 : Artifact.submissionArtifact.instructionPC 18 = 30 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_13 : Artifact.submissionArtifact.instructionPC 19 = 32 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_14 : Artifact.submissionArtifact.instructionPC 20 = 33 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_15 : Artifact.submissionArtifact.instructionPC 21 = 34 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_16 : Artifact.submissionArtifact.instructionPC 22 = 37 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_17 : Artifact.submissionArtifact.instructionPC 23 = 38 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_18 : Artifact.submissionArtifact.instructionPC 24 = 39 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_19 : Artifact.submissionArtifact.instructionPC 25 = 40 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_20 : Artifact.submissionArtifact.instructionPC 26 = 42 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_21 : Artifact.submissionArtifact.instructionPC 27 = 44 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_22 : Artifact.submissionArtifact.instructionPC 28 = 45 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_23 : Artifact.submissionArtifact.instructionPC 29 = 46 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_24 : Artifact.submissionArtifact.instructionPC 30 = 47 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_25 : Artifact.submissionArtifact.instructionPC 31 = 48 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_26 : Artifact.submissionArtifact.instructionPC 32 = 49 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_27 : Artifact.submissionArtifact.instructionPC 33 = 52 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_28 : Artifact.submissionArtifact.instructionPC 34 = 53 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_29 : Artifact.submissionArtifact.instructionPC 34 = 53 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_30 : Artifact.submissionArtifact.instructionPC 34 = 53 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_31 : Artifact.submissionArtifact.instructionPC 35 = 54 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_32 : Artifact.submissionArtifact.instructionPC 36 = 55 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_33 : Artifact.submissionArtifact.instructionPC 37 = 58 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_34 : Artifact.submissionArtifact.instructionPC 38 = 61 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_35 : Artifact.submissionArtifact.instructionPC 39 = 62 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_36 : Artifact.submissionArtifact.instructionPC 40 = 63 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_38 : Artifact.submissionArtifact.instructionPC 41 = 64 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_39 : Artifact.submissionArtifact.instructionPC 42 = 65 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_40 : Artifact.submissionArtifact.instructionPC 43 = 67 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_41 : Artifact.submissionArtifact.instructionPC 44 = 68 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_42 : Artifact.submissionArtifact.instructionPC 45 = 69 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_43 : Artifact.submissionArtifact.instructionPC 46 = 70 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_44 : Artifact.submissionArtifact.instructionPC 47 = 71 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_45 : Artifact.submissionArtifact.instructionPC 48 = 72 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_46 : Artifact.submissionArtifact.instructionPC 49 = 73 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_47 : Artifact.submissionArtifact.instructionPC 50 = 75 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_48 : Artifact.submissionArtifact.instructionPC 51 = 76 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_49 : Artifact.submissionArtifact.instructionPC 52 = 77 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_50 : Artifact.submissionArtifact.instructionPC 53 = 78 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_51 : Artifact.submissionArtifact.instructionPC 54 = 79 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_52 : Artifact.submissionArtifact.instructionPC 55 = 80 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_53 : Artifact.submissionArtifact.instructionPC 56 = 81 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_54 : Artifact.submissionArtifact.instructionPC 57 = 82 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_55 : Artifact.submissionArtifact.instructionPC 58 = 83 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_56 : Artifact.submissionArtifact.instructionPC 59 = 85 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_57 : Artifact.submissionArtifact.instructionPC 60 = 86 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_58 : Artifact.submissionArtifact.instructionPC 61 = 88 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_59 : Artifact.submissionArtifact.instructionPC 62 = 89 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_60 : Artifact.submissionArtifact.instructionPC 63 = 110 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_61 : Artifact.submissionArtifact.instructionPC 64 = 111 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_62 : Artifact.submissionArtifact.instructionPC 65 = 112 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_63 : Artifact.submissionArtifact.instructionPC 66 = 113 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_64 : Artifact.submissionArtifact.instructionPC 67 = 114 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_65 : Artifact.submissionArtifact.instructionPC 68 = 115 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_66 : Artifact.submissionArtifact.instructionPC 69 = 116 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_67 : Artifact.submissionArtifact.instructionPC 70 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_68 : Artifact.submissionArtifact.instructionPC 70 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_69 : Artifact.submissionArtifact.instructionPC 71 = 120 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_70 : Artifact.submissionArtifact.instructionPC 72 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_71 : Artifact.submissionArtifact.instructionPC 73 = 122 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_72 : Artifact.submissionArtifact.instructionPC 74 = 123 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem producerEndPC : Artifact.submissionArtifact.instructionPC 31 = 48 := pc_direct_25
@[simp] theorem earlyWordLoadPC : Artifact.submissionArtifact.instructionPC 32 = 49 := pc_direct_26
@[simp] theorem pc2823 : Artifact.submissionArtifact.instructionPC 33 = 52 := pc_direct_27
@[simp] theorem pc2824 : Artifact.submissionArtifact.instructionPC 34 = 53 := pc_direct_28
@[simp] theorem pc2825 : Artifact.submissionArtifact.instructionPC 34 = 53 := pc_direct_29
@[simp] theorem pc2860 : Artifact.submissionArtifact.instructionPC 73 = 122 := pc_direct_71
@[simp] theorem pc_classifier_112 : Artifact.submissionArtifact.instructionPC 23 = 38 := pc_direct_17
@[simp] theorem pc_classifier_113 : Artifact.submissionArtifact.instructionPC 24 = 39 := pc_direct_18

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
