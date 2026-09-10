import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128GuardLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128GuardTrace
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

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


def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }
def guardEntry (input : ByteArray) : State := atPC input 5261
def fallbackState (input : ByteArray) : State := atPC input 368
def firstByte (input : ByteArray) : Nat :=
  (YulSemantics.EVM.byteFrom input.toList 0).toNat
abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)
@[simp] theorem initialState_halt (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).halt = .Running := rfl
@[simp] theorem initialState_code (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.code = code := rfl
@[simp] theorem zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
attribute [simp] Challenge.Ripemd160.initialState_stack
  Challenge.Ripemd160.initialState_pc Challenge.Ripemd160.initialState_calldata

@[simp] theorem pc_4116 : Artifact.submissionArtifact.instructionPC 4112 = 5261 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4117 : Artifact.submissionArtifact.instructionPC 4113 = 5262 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4118 : Artifact.submissionArtifact.instructionPC 4114 = 5263 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4119 : Artifact.submissionArtifact.instructionPC 4115 = 5265 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4120 : Artifact.submissionArtifact.instructionPC 4116 = 5266 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4121 : Artifact.submissionArtifact.instructionPC 4117 = 5267 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4122 : Artifact.submissionArtifact.instructionPC 4118 = 5268 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4123 : Artifact.submissionArtifact.instructionPC 4119 = 5269 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4124 : Artifact.submissionArtifact.instructionPC 4120 = 5270 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4125 : Artifact.submissionArtifact.instructionPC 4121 = 5271 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4126 : Artifact.submissionArtifact.instructionPC 4122 = 5273 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4127 : Artifact.submissionArtifact.instructionPC 4123 = 5274 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4128 : Artifact.submissionArtifact.instructionPC 4124 = 5275 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4129 : Artifact.submissionArtifact.instructionPC 4125 = 5276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4130 : Artifact.submissionArtifact.instructionPC 4126 = 5279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4131 : Artifact.submissionArtifact.instructionPC 4127 = 5280 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4132 : Artifact.submissionArtifact.instructionPC 4128 = 5281 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4133 : Artifact.submissionArtifact.instructionPC 4129 = 5283 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_61 : Artifact.submissionArtifact.instructionPC 61 = 101 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_62 : Artifact.submissionArtifact.instructionPC 62 = 102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def guardCheckPath : List Located :=
  [opAt 4112 .JUMPDEST,
   opAt 4113 .CALLDATASIZE,
   pushAt 4114 1 128,
   opAt 4115 .XOR,
   opAt 4116 .JUMPDEST,
   pushAt 4117 0 0,
   opAt 4118 .CALLDATALOAD,
   pushAt 4119 0 0,
   opAt 4120 .BYTE,
   pushAt 4121 1 7,
   opAt 4122 .XOR,
   opAt 4123 .JUMPDEST,
   opAt 4124 .OR,
   pushAt 4125 2 368,
   opAt 4126 .JUMPI]

def guardMatchSuffix : List Located :=
  [pushAt 4127 0 0,
   pushAt 4128 1 101,
   opAt 4129 .JUMP]

def guardMatchTail : List Located :=
  [opAt 61 .JUMPDEST, opAt 62 .POP]

def guardJumpState (input : ByteArray) : State :=
  { guardEntry input with
    pc := UInt256.ofNat 101
    stack := [UInt256.ofNat 0] }

theorem firstByte_eq_byteAt (input : ByteArray) :
    UInt256.byteAt (⟨0⟩ : UInt256) (MachineState.readWord input 0) =
      UInt256.ofNat (firstByte input) := by
  simpa [firstByte] using
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input 0)

def guardDiff (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor (UInt256.ofNat 7) (UInt256.ofNat (firstByte input)))
    (UInt256.xor (UInt256.ofNat 128) (UInt256.ofNat input.size))

theorem guardDiff_eq_zero_iff (input : ByteArray) (hfit : CalldataFits input) :
    guardDiff input = 0 ↔ input.size = 128 ∧ firstByte input = 7 := by
  have hsize : input.size < 2^256 := Nat.lt_trans hfit (by norm_num)
  have hbyte : firstByte input < 2^256 := by
    unfold firstByte
    exact Nat.lt_trans (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt (by norm_num)
  simp only [guardDiff, Patterned128GuardLogic.wordOr_eq_zero_iff,
    Patterned128GuardLogic.wordXor_eq_zero_iff,
    Patterned128GuardLogic.ofNat_eq_iff (by norm_num : 7 < 2^256) hbyte,
    Patterned128GuardLogic.ofNat_eq_iff (by norm_num : 128 < 2^256) hsize]
  omega

theorem guard_fallback_dest :
    Decode.isValidJumpDest submissionBytecode 368 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 205 (by rfl)

theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 101 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 61 (by rfl)

theorem run_guard_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 128 ∨ firstByte input ≠ 7) :
    run guardCheckPath (guardEntry input) =
      some (fallbackState input) := by
  have hne : guardDiff input ≠ 0 := by
    intro hz
    have h := (guardDiff_eq_zero_iff input hfit).1 hz
    rcases hbad with hbad | hbad
    · exact hbad h.1
    · exact hbad h.2
  have htrue : UInt256.isTrue (guardDiff input) :=
    Patterned128GuardLogic.isTrue_of_ne_zero _ hne
  simp only [guardDiff] at htrue
  simp (config := { decide := true })
    [guardCheckPath, opAt, pushAt, wfOp,
     guardEntry, fallbackState, atPC,
     htrue, guard_fallback_dest, List.exchange,
     Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, firstByte_eq_byteAt]

theorem run_guard_match_helper (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) (hbyte : firstByte input = 7) :
    run (guardCheckPath ++ guardMatchSuffix)
      (guardEntry input) = some (guardJumpState input) := by
  have hzero := (guardDiff_eq_zero_iff input hfit).2 ⟨hsize, hbyte⟩
  simp only [guardDiff] at hzero
  simp (config := { decide := true })
    [guardCheckPath, guardMatchSuffix, opAt, pushAt,
     wfOp, guardEntry, guardJumpState, atPC,
     hzero, guard_match_dest, UInt256.isTrue, List.exchange,
     Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat, firstByte_eq_byteAt]


#print axioms run_guard_fail
#print axioms run_guard_match_helper
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128GuardTrace
