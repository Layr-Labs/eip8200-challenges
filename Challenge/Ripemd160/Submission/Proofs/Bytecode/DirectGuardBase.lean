import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcEncoding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RepeatedByteWord
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardGrouping
import Challenge.Ripemd160.Submission.Proofs.Bytecode.EqualityAccumulator
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
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.DataStepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.DataStepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.DataStepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

/-- Exact size gate: `1000 - size != 0` jumps to the patterned guard at 4565. -/
def sizePrefix : List Located :=
  [opAt 6 .CALLDATASIZE,
   pushAt 7 2 1000,
   opAt 8 .SUB,
   pushAt 9 2 4565]

/-- Anchor gate: `97 + 255 * calldata[0] != 0` (first word is not the repeated
`0x61` word) jumps straight to the recogniser's private 1000-byte row at 8158 (the size is
already known to be 1000 here). -/
def anchorPrefix : List Located :=
  [pushAt 11 0 0,
   opAt 12 .CALLDATALOAD,
   pushAt 13 1 255,
   opAt 14 .MUL,
   pushAt 15 1 97,
   opAt 16 .ADD,
   pushAt 17 2 8158]

def entryDest : Located := opAt 154 .JUMPDEST

/-- The reference word and the tail word seed the accumulator. -/
def checkEntryPath : List Located :=
  [pushAt 19 0 0,
   opAt 20 .MLOAD,
   opAt 21 .CALLDATALOAD,
   pushAt 22 2 968,
   opAt 23 .CALLDATALOAD,
   opAt 24 (.Dup ⟨1, by decide⟩),
   opAt 25 .EQ]

/-- The matching edge drops the comparison accumulator; no legacy zero is live. -/
def tailPath : List Located :=
  [pushAt 5411 3 4706,
   opAt 5412 .JUMPI]

/-- Off the measured path: the divert lands on the generic arm's entry. -/
def fallbackPath : List Located :=
  [pushAt 5413 0 0, pushAt 5414 1 245, opAt 5415 .JUMP, entryDest]

def returnPath : List Located :=
  [pushAt 3458 20 972889429405991776604892044862621566948497025487,
   pushAt 3459 0 0,
   opAt 3460 .MSTORE]

def returnFinishPath : List Located :=
  [pushAt 3462 0 0,
   opAt 3463 .RETURN]

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

def sizeMatched (input : ByteArray) : State := atPC input 33

def spentCells (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat 0, referenceWord input]

/-- Only the generic miss adapter needs the legacy zero counter. -/
def returnCells (input : ByteArray) : List UInt256 :=
  [referenceWord input]

def fallbackState (input : ByteArray) : State :=
  StackTail.append ({ atPC input 246 with activeWords := UInt256.ofNat 1 }) (spentCells input)

/-- Counter-free scanner entry; the legacy loop counter is restored only on a miss. -/
def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9429
    activeWords := UInt256.ofNat 1
    stack := [equalityAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9633
    activeWords := UInt256.ofNat 1
    stack := [equalityAcc input 10, referenceWord input] }

/-- The equality-accumulator branch at PC9637 jumps to answer `JUMPDEST` 4706. -/
def returnHopState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4706
    activeWords := UInt256.ofNat 1
    stack := returnCells input }

def returnHopPath : List Located :=
  [opAt 3457 .JUMPDEST]

def returnEntry (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4707
    activeWords := UInt256.ofNat 1
    stack := returnCells input }

def tailDivertState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 9638
    activeWords := UInt256.ofNat 1
    stack := returnCells input }

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4732
    stack := returnCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def storedReturnState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4730
    stack := returnCells input
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def sizedReturnState (input : ByteArray) : State :=
  { storedReturnState input with
    pc := UInt256.ofNat 4731
    stack := UInt256.ofNat 32 :: returnCells input }

abbrev run := Challenge.EvmProof.DataStepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/- Freeze the exact concrete instruction PCs used by the guard. -/
@[simp] theorem pc_direct_6 : Artifact.submissionArtifact.instructionPC 6 = 12 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_7 : Artifact.submissionArtifact.instructionPC 7 = 13 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_8 : Artifact.submissionArtifact.instructionPC 8 = 16 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_9 : Artifact.submissionArtifact.instructionPC 9 = 17 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_10 : Artifact.submissionArtifact.instructionPC 10 = 20 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_11 : Artifact.submissionArtifact.instructionPC 11 = 21 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_12 : Artifact.submissionArtifact.instructionPC 12 = 22 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_13 : Artifact.submissionArtifact.instructionPC 13 = 23 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_14 : Artifact.submissionArtifact.instructionPC 14 = 25 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_15 : Artifact.submissionArtifact.instructionPC 15 = 26 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_16 : Artifact.submissionArtifact.instructionPC 16 = 28 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_17 : Artifact.submissionArtifact.instructionPC 17 = 29 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_18 : Artifact.submissionArtifact.instructionPC 18 = 32 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_19 : Artifact.submissionArtifact.instructionPC 19 = 33 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_20 : Artifact.submissionArtifact.instructionPC 20 = 34 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_21 : Artifact.submissionArtifact.instructionPC 22 = 36 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_22 : Artifact.submissionArtifact.instructionPC 23 = 39 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_23 : Artifact.submissionArtifact.instructionPC 24 = 40 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_24 : Artifact.submissionArtifact.instructionPC 25 = 41 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_25 : Artifact.submissionArtifact.instructionPC 26 = 42 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_26 : Artifact.submissionArtifact.instructionPC 125 = 210 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_27 : Artifact.submissionArtifact.instructionPC 126 = 211 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_28 : Artifact.submissionArtifact.instructionPC 127 = 214 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_29 : Artifact.submissionArtifact.instructionPC 128 = 215 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_30 : Artifact.submissionArtifact.instructionPC 129 = 216 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_31 : Artifact.submissionArtifact.instructionPC 130 = 217 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_32 : Artifact.submissionArtifact.instructionPC 131 = 218 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_33 : Artifact.submissionArtifact.instructionPC 132 = 219 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_34 : Artifact.submissionArtifact.instructionPC 133 = 220 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_35 : Artifact.submissionArtifact.instructionPC 134 = 221 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_36 : Artifact.submissionArtifact.instructionPC 135 = 222 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_37 : Artifact.submissionArtifact.instructionPC 136 = 223 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_38 : Artifact.submissionArtifact.instructionPC 137 = 224 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_39 : Artifact.submissionArtifact.instructionPC 138 = 225 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_40 : Artifact.submissionArtifact.instructionPC 139 = 226 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_41 : Artifact.submissionArtifact.instructionPC 140 = 227 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_42 : Artifact.submissionArtifact.instructionPC 141 = 229 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_43 : Artifact.submissionArtifact.instructionPC 142 = 230 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_44 : Artifact.submissionArtifact.instructionPC 143 = 231 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_45 : Artifact.submissionArtifact.instructionPC 144 = 232 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_46 : Artifact.submissionArtifact.instructionPC 145 = 233 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_47 : Artifact.submissionArtifact.instructionPC 146 = 234 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_48 : Artifact.submissionArtifact.instructionPC 147 = 235 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_49 : Artifact.submissionArtifact.instructionPC 148 = 236 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_50 : Artifact.submissionArtifact.instructionPC 149 = 237 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_51 : Artifact.submissionArtifact.instructionPC 150 = 239 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_52 : Artifact.submissionArtifact.instructionPC 157 = 309 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_53 : Artifact.submissionArtifact.instructionPC 153 = 244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_54 : Artifact.submissionArtifact.instructionPC 3458 = 4707 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_55 : Artifact.submissionArtifact.instructionPC 3458 = 4707 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_56 : Artifact.submissionArtifact.instructionPC 3459 = 4728 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_57 : Artifact.submissionArtifact.instructionPC 3460 = 4729 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_58 : Artifact.submissionArtifact.instructionPC 3461 = 4730 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_59 : Artifact.submissionArtifact.instructionPC 3462 = 4731 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_60 : Artifact.submissionArtifact.instructionPC 3463 = 4732 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_61 : Artifact.submissionArtifact.instructionPC 58 = 93 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_62 : Artifact.submissionArtifact.instructionPC 62 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_63 : Artifact.submissionArtifact.instructionPC 63 = 120 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_64 : Artifact.submissionArtifact.instructionPC 64 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_65 : Artifact.submissionArtifact.instructionPC 62 = 117 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_66 : Artifact.submissionArtifact.instructionPC 63 = 120 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_67 : Artifact.submissionArtifact.instructionPC 64 = 121 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_68 : Artifact.submissionArtifact.instructionPC 88 = 156 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_69 : Artifact.submissionArtifact.instructionPC 89 = 157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_70 : Artifact.submissionArtifact.instructionPC 90 = 159 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_71 : Artifact.submissionArtifact.instructionPC 91 = 160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_72 : Artifact.submissionArtifact.instructionPC 92 = 164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_73 : Artifact.submissionArtifact.instructionPC 3397 = 4547 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_74 : Artifact.submissionArtifact.instructionPC 3398 = 4548 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

@[simp] theorem pc_direct_75 : Artifact.submissionArtifact.instructionPC 151 = 240 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_76 : Artifact.submissionArtifact.instructionPC 152 = 243 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_77 : Artifact.submissionArtifact.instructionPC 153 = 244 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_direct_78 : Artifact.submissionArtifact.instructionPC 3457 = 4706 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
