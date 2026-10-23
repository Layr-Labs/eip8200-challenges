import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PcSeedRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.KnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Execution
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.DirectGuardGrouping
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.EqualityAccumulator
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open HoistedInherited.KnownInputCompactState
@[simp] private theorem literalZeroWord : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := rfl
@[simp] private theorem zeroWordNat : (0 : UInt256).toNat = 0 := rfl

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.DataStepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.DataStepper.Located HoistedInherited.Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : HoistedInherited.Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : HoistedInherited.Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.DataStepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

/-- Exact size gate: `1000 - size != 0` jumps to the patterned guard at 4583. -/
def sizePrefix : List Located :=
  [opAt 6 .CALLDATASIZE,
   pushAt 7 2 1000,
   opAt 8 .SUB,
   pushAt 9 2 4583]

/-- Anchor gate: low 64 bits of calldata[0] other than `0x61` jump straight to
the recogniser's private 1000-byte row at 8157 (the size is already 1000). -/
def anchorPrefix : List Located :=
  [pushAt 11 0 0,
   opAt 12 .CALLDATALOAD,
   opAt 13 (.Dup ⟨0, by decide⟩),
   pushAt 14 15 0x6161616161616161,
   opAt 15 .XOR,
   pushAt 16 1 192,
   opAt 17 .SHL,
   pushAt 18 2 8157]

def entryDest : Located := opAt 125 .JUMPDEST

/-- The reference word and the tail word seed the accumulator. -/
def checkEntryPath : List Located :=
  [opAt 20 .PC,
   opAt 21 .CALLDATALOAD,
   opAt 22 (.Dup ⟨1, by decide⟩),
   opAt 23 .EQ]

/-- The matching edge drops the comparison accumulator; no legacy zero is live. -/
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

def sizeMatched (input : ByteArray) : State :=
  {atPC input 48 with stack := [MachineState.readWord input 0]}

def spentCells (_input : ByteArray) : List UInt256 :=
  []

/-- The terminal comparison consumes the reference; no repeated-route suffix remains. -/
def returnCells (_input : ByteArray) : List UInt256 :=
  []

/-- Only the miss cleanup PUSH0 survives into the generic backend, not the reference word. -/
def genericMissCells (input : ByteArray) : List UInt256 :=
  UInt256.ofNat 0 :: spentCells input

def fallbackState (input : ByteArray) : State :=
  StackTail.append ({ atPC input 246 with activeWords := UInt256.ofNat 0 }) (genericMissCells input)

/-- Counter-free scanner entry; terminal MUL consumes both the accumulator and reference. -/
def loopState (input : ByteArray) (_n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9429
    activeWords := UInt256.ofNat 0
    stack := [HoistedInherited.PcSeedRaw.seed input, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9632
    activeWords := UInt256.ofNat 0
    stack := [HoistedInherited.PcSeedRaw.mismatch input] }

/-- The equality-accumulator branch at PC9636 jumps to answer `JUMPDEST` 4706. -/
def returnHopState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9636
    activeWords := UInt256.ofNat 0
    stack := returnCells input }

def returnHopPath : List Located := []

def returnEntry (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9636
    activeWords := UInt256.ofNat 0
    stack := returnCells input }

def tailDivertState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9662
    activeWords := UInt256.ofNat 0
    stack := returnCells input }

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9661
    stack := returnCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storedReturnState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9659
    stack := returnCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedReturnState (input : ByteArray) : State :=
  { storedReturnState input with
    pc := UInt256.ofNat 9660
    stack := UInt256.ofNat 32 :: returnCells input }

abbrev run := Challenge.EvmProof.DataStepper.runLocatedBlock
  (artifact := HoistedInherited.Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the exact concrete instruction PCs used by the guard. -/
@[simp] theorem pc_direct_6 : HoistedInherited.Artifact.submissionArtifact.instructionPC 6 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_7 : HoistedInherited.Artifact.submissionArtifact.instructionPC 7 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_8 : HoistedInherited.Artifact.submissionArtifact.instructionPC 8 = 16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_9 : HoistedInherited.Artifact.submissionArtifact.instructionPC 9 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_10 : HoistedInherited.Artifact.submissionArtifact.instructionPC 10 = 20 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_11 : HoistedInherited.Artifact.submissionArtifact.instructionPC 11 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_12 : HoistedInherited.Artifact.submissionArtifact.instructionPC 12 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_13 : HoistedInherited.Artifact.submissionArtifact.instructionPC 13 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_14 : HoistedInherited.Artifact.submissionArtifact.instructionPC 14 = 24 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_15 : HoistedInherited.Artifact.submissionArtifact.instructionPC 15 = 40 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_16 : HoistedInherited.Artifact.submissionArtifact.instructionPC 16 = 41 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_17 : HoistedInherited.Artifact.submissionArtifact.instructionPC 17 = 43 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_18 : HoistedInherited.Artifact.submissionArtifact.instructionPC 18 = 44 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_19 : HoistedInherited.Artifact.submissionArtifact.instructionPC 19 = 47 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_20 : HoistedInherited.Artifact.submissionArtifact.instructionPC 20 = 48 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_21 : HoistedInherited.Artifact.submissionArtifact.instructionPC 22 = 50 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_22 : HoistedInherited.Artifact.submissionArtifact.instructionPC 23 = 51 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_23 : HoistedInherited.Artifact.submissionArtifact.instructionPC 24 = 52 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_24 : HoistedInherited.Artifact.submissionArtifact.instructionPC 25 = 55 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_25 : HoistedInherited.Artifact.submissionArtifact.instructionPC 21 = 49 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_26 : HoistedInherited.Artifact.submissionArtifact.instructionPC 98 = 210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_27 : HoistedInherited.Artifact.submissionArtifact.instructionPC 99 = 211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_28 : HoistedInherited.Artifact.submissionArtifact.instructionPC 102 = 214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_29 : HoistedInherited.Artifact.submissionArtifact.instructionPC 103 = 216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_30 : HoistedInherited.Artifact.submissionArtifact.instructionPC 103 = 216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_31 : HoistedInherited.Artifact.submissionArtifact.instructionPC 104 = 217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_32 : HoistedInherited.Artifact.submissionArtifact.instructionPC 105 = 218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_33 : HoistedInherited.Artifact.submissionArtifact.instructionPC 106 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_34 : HoistedInherited.Artifact.submissionArtifact.instructionPC 106 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_35 : HoistedInherited.Artifact.submissionArtifact.instructionPC 106 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_36 : HoistedInherited.Artifact.submissionArtifact.instructionPC 107 = 222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_37 : HoistedInherited.Artifact.submissionArtifact.instructionPC 110 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_38 : HoistedInherited.Artifact.submissionArtifact.instructionPC 110 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_39 : HoistedInherited.Artifact.submissionArtifact.instructionPC 109 = 225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_40 : HoistedInherited.Artifact.submissionArtifact.instructionPC 110 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_41 : HoistedInherited.Artifact.submissionArtifact.instructionPC 111 = 227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_42 : HoistedInherited.Artifact.submissionArtifact.instructionPC 113 = 229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_43 : HoistedInherited.Artifact.submissionArtifact.instructionPC 116 = 235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_44 : HoistedInherited.Artifact.submissionArtifact.instructionPC 117 = 237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_45 : HoistedInherited.Artifact.submissionArtifact.instructionPC 114 = 232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_46 : HoistedInherited.Artifact.submissionArtifact.instructionPC 115 = 233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_47 : HoistedInherited.Artifact.submissionArtifact.instructionPC 120 = 240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_48 : HoistedInherited.Artifact.submissionArtifact.instructionPC 116 = 235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_49 : HoistedInherited.Artifact.submissionArtifact.instructionPC 122 = 242 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_50 : HoistedInherited.Artifact.submissionArtifact.instructionPC 117 = 237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_51 : HoistedInherited.Artifact.submissionArtifact.instructionPC 119 = 239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_52 : HoistedInherited.Artifact.submissionArtifact.instructionPC 128 = 309 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_53 : HoistedInherited.Artifact.submissionArtifact.instructionPC 124 = 244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_54 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3423 = 4737 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_55 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3423 = 4737 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_56 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3424 = 4738 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_57 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3425 = 4739 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_58 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3426 = 4740 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_59 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3427 = 4742 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_60 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3428 = 4743 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_61 : HoistedInherited.Artifact.submissionArtifact.instructionPC 52 = 93 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_62 : HoistedInherited.Artifact.submissionArtifact.instructionPC 56 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_63 : HoistedInherited.Artifact.submissionArtifact.instructionPC 57 = 120 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_64 : HoistedInherited.Artifact.submissionArtifact.instructionPC 58 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_65 : HoistedInherited.Artifact.submissionArtifact.instructionPC 56 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_66 : HoistedInherited.Artifact.submissionArtifact.instructionPC 57 = 120 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_67 : HoistedInherited.Artifact.submissionArtifact.instructionPC 58 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_68 : HoistedInherited.Artifact.submissionArtifact.instructionPC 81 = 184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_69 : HoistedInherited.Artifact.submissionArtifact.instructionPC 82 = 187 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_70 : HoistedInherited.Artifact.submissionArtifact.instructionPC 82 = 187 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_72 : HoistedInherited.Artifact.submissionArtifact.instructionPC 83 = 188 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_73 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3368 = 4565 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_74 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3369 = 4566 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem pc_direct_75 : HoistedInherited.Artifact.submissionArtifact.instructionPC 120 = 240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_76 : HoistedInherited.Artifact.submissionArtifact.instructionPC 123 = 243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_77 : HoistedInherited.Artifact.submissionArtifact.instructionPC 124 = 244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_78 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3422 = 4736 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.DirectGuard
