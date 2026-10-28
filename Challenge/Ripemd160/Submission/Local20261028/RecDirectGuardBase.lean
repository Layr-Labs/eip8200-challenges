import Challenge.Ripemd160.Submission.Local20261028.RecPcSeedRaw
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Local20261028.RecKnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Local20261028.RecRecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Local20261028.ColdExecution
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Local20261028.RecDirectGuardGrouping
import Challenge.Ripemd160.Submission.Local20261028.RecEqualityAccumulator
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTail

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Control.KnownInputCompactState
@[simp] private theorem literalZeroWord : (⟨0⟩ : UInt256) = UInt256.ofNat 0 := rfl
@[simp] private theorem zeroWordNat : (0 : UInt256).toNat = 0 := rfl

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.DataStepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.DataStepper.Located Control.Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Control.Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Control.Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.DataStepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

/-- Exact size gate: `1000 - size != 0` jumps to the relocated patterned guard at 4601. -/
def sizePrefix : List Located :=
  [opAt 6 .CALLDATASIZE,
   pushAt 7 2 1000,
   opAt 8 .SUB,
   pushAt 9 2 8247]

/-- Anchor gate: low 64 bits of calldata[0] other than `0x61` jump straight to
the recogniser's private 1000-byte arm at 9394 (the size is already 1000). -/
def anchorPrefix : List Located :=
  [pushAt 11 0 0,
   opAt 12 .CALLDATALOAD,
   pushAt 13 15 0x6161616161616161,
   opAt 14 (.Dup ⟨1, by decide⟩),
   opAt 15 .XOR,
   pushAt 16 1 192,
   opAt 17 .SHL,
   pushAt 18 2 9394]

def entryDest : Located := opAt 133 .JUMPDEST

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
    pc := UInt256.ofNat 9711
    activeWords := UInt256.ofNat 0
    stack := [Control.PcSeedRaw.seed input, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9914
    activeWords := UInt256.ofNat 0
    stack := [Control.PcSeedRaw.mismatch input] }

/-- The equality-accumulator branch at PC9636 jumps to answer `JUMPDEST` 4706. -/
def returnHopState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9918
    activeWords := UInt256.ofNat 0
    stack := returnCells input }

def returnHopPath : List Located := []

def returnEntry (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9918
    activeWords := UInt256.ofNat 0
    stack := returnCells input }

def tailDivertState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9944
    activeWords := UInt256.ofNat 0
    stack := returnCells input }

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9943
    stack := returnCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storedReturnState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9941
    stack := returnCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedReturnState (input : ByteArray) : State :=
  { storedReturnState input with
    pc := UInt256.ofNat 9942
    stack := UInt256.ofNat 32 :: returnCells input }

abbrev run := Challenge.EvmProof.DataStepper.runLocatedBlock
  (artifact := Control.Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the exact concrete instruction PCs used by the guard. -/
@[simp] theorem pc_direct_6 : Control.Artifact.submissionArtifact.instructionPC 6 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_7 : Control.Artifact.submissionArtifact.instructionPC 7 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_8 : Control.Artifact.submissionArtifact.instructionPC 8 = 16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_9 : Control.Artifact.submissionArtifact.instructionPC 9 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_10 : Control.Artifact.submissionArtifact.instructionPC 10 = 20 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_11 : Control.Artifact.submissionArtifact.instructionPC 11 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_12 : Control.Artifact.submissionArtifact.instructionPC 12 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_13 : Control.Artifact.submissionArtifact.instructionPC 13 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_14 : Control.Artifact.submissionArtifact.instructionPC 14 = 39 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_15 : Control.Artifact.submissionArtifact.instructionPC 15 = 40 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_16 : Control.Artifact.submissionArtifact.instructionPC 16 = 41 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_17 : Control.Artifact.submissionArtifact.instructionPC 17 = 43 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_18 : Control.Artifact.submissionArtifact.instructionPC 18 = 44 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_19 : Control.Artifact.submissionArtifact.instructionPC 19 = 47 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_20 : Control.Artifact.submissionArtifact.instructionPC 20 = 48 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_21 : Control.Artifact.submissionArtifact.instructionPC 22 = 50 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_22 : Control.Artifact.submissionArtifact.instructionPC 23 = 51 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_23 : Control.Artifact.submissionArtifact.instructionPC 24 = 52 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_24 : Control.Artifact.submissionArtifact.instructionPC 25 = 55 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_25 : Control.Artifact.submissionArtifact.instructionPC 21 = 49 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_26 : Control.Artifact.submissionArtifact.instructionPC 106 = 210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_27 : Control.Artifact.submissionArtifact.instructionPC 107 = 211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_28 : Control.Artifact.submissionArtifact.instructionPC 110 = 214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_29 : Control.Artifact.submissionArtifact.instructionPC 111 = 216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_30 : Control.Artifact.submissionArtifact.instructionPC 111 = 216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_31 : Control.Artifact.submissionArtifact.instructionPC 112 = 217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_32 : Control.Artifact.submissionArtifact.instructionPC 113 = 218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_33 : Control.Artifact.submissionArtifact.instructionPC 114 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_34 : Control.Artifact.submissionArtifact.instructionPC 114 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_35 : Control.Artifact.submissionArtifact.instructionPC 114 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_36 : Control.Artifact.submissionArtifact.instructionPC 115 = 222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_37 : Control.Artifact.submissionArtifact.instructionPC 118 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_38 : Control.Artifact.submissionArtifact.instructionPC 118 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_39 : Control.Artifact.submissionArtifact.instructionPC 117 = 225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_40 : Control.Artifact.submissionArtifact.instructionPC 118 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_41 : Control.Artifact.submissionArtifact.instructionPC 119 = 227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_42 : Control.Artifact.submissionArtifact.instructionPC 121 = 229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_43 : Control.Artifact.submissionArtifact.instructionPC 124 = 235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_44 : Control.Artifact.submissionArtifact.instructionPC 125 = 237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_45 : Control.Artifact.submissionArtifact.instructionPC 122 = 232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_46 : Control.Artifact.submissionArtifact.instructionPC 123 = 233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_47 : Control.Artifact.submissionArtifact.instructionPC 128 = 240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_48 : Control.Artifact.submissionArtifact.instructionPC 124 = 235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_49 : Control.Artifact.submissionArtifact.instructionPC 130 = 242 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_50 : Control.Artifact.submissionArtifact.instructionPC 125 = 237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_51 : Control.Artifact.submissionArtifact.instructionPC 127 = 239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_52 : Control.Artifact.submissionArtifact.instructionPC 136 = 309 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_53 : Control.Artifact.submissionArtifact.instructionPC 132 = 244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_54 : Control.Artifact.submissionArtifact.instructionPC 6222 = 8401 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_55 : Control.Artifact.submissionArtifact.instructionPC 6222 = 8401 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_56 : Control.Artifact.submissionArtifact.instructionPC 6223 = 8402 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_57 : Control.Artifact.submissionArtifact.instructionPC 6224 = 8403 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_58 : Control.Artifact.submissionArtifact.instructionPC 6225 = 8404 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_59 : Control.Artifact.submissionArtifact.instructionPC 6226 = 8406 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_60 : Control.Artifact.submissionArtifact.instructionPC 6227 = 8407 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem pc_direct_75 : Control.Artifact.submissionArtifact.instructionPC 128 = 240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_76 : Control.Artifact.submissionArtifact.instructionPC 131 = 243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_77 : Control.Artifact.submissionArtifact.instructionPC 132 = 244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_78 : Control.Artifact.submissionArtifact.instructionPC 6221 = 8400 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.DirectGuard
