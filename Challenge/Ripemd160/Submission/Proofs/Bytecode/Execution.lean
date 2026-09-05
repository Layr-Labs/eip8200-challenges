import Batteries.Tactic.OpenPrivate
import Challenge.EvmProof.Stepper
import Challenge.EvmProof.Word
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactSegment
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def mainStart (input : ByteArray) : State := atPC input 0x03ef

/-! ## Empty dispatcher PCs (frozen 4955-byte / 2882-instruction artifact).

The new tail appends ten instructions at `0x133a` (indices `2872..2881`).
Bounds use the 33-byte suffix certificate; no whole-prefix `decide` over
2872+ instructions. Fixed prefix bytes preserved. -/

open private
  submissionInstructionsChunk0 submissionInstructionsChunk1
  submissionInstructionsChunk2 submissionInstructionsChunk3
  submissionInstructionsChunk4 submissionInstructionsChunk5
  submissionInstructionsChunk6 submissionInstructionsChunk7
  submissionInstructionsChunk8 submissionInstructionsChunk9
  submissionInstructionsChunk10 submissionInstructionsChunk11
  submissionInstructionsChunk12 submissionInstructionsChunk13
  submissionInstructionsChunk14 submissionInstructionsChunk15
  submissionInstructionsChunk16
  submissionInstructionsChunk0_length submissionInstructionsChunk1_length
  submissionInstructionsChunk2_length submissionInstructionsChunk3_length
  submissionInstructionsChunk4_length submissionInstructionsChunk5_length
  submissionInstructionsChunk6_length submissionInstructionsChunk7_length
  submissionInstructionsChunk8_length submissionInstructionsChunk9_length
  submissionInstructionsChunk10_length submissionInstructionsChunk11_length
  submissionInstructionsChunk12_length submissionInstructionsChunk13_length
  submissionInstructionsChunk14_length submissionInstructionsChunk15_length
  submissionInstructionsChunk16_length
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

private def dispatchPrefix : List YulEvmCompiler.Instr :=
  Artifact.submissionInstructions.take 2872

private def dispatchSuffix : List YulEvmCompiler.Instr :=
  Artifact.submissionInstructions.drop 2872

private theorem dispatchPrefix_length : dispatchPrefix.length = 2872 := by
  simp only [dispatchPrefix, List.length_take, Artifact.referenceInstructions_count]
  decide

private theorem dispatchSuffix_length : dispatchSuffix.length = 10 := by
  simp only [dispatchSuffix, List.length_drop, Artifact.referenceInstructions_count]

private theorem dispatchSuffix_eq :
    dispatchSuffix = submissionInstructionsChunk15 := by
  simp only [dispatchSuffix, Artifact.submissionInstructions]
  repeat' (first
    | rw [List.drop_left]
    | rw [List.drop_drop]
    | rw [submissionInstructionsChunk0_length]
    | rw [submissionInstructionsChunk1_length]
    | rw [submissionInstructionsChunk2_length]
    | rw [submissionInstructionsChunk3_length]
    | rw [submissionInstructionsChunk4_length]
    | rw [submissionInstructionsChunk5_length]
    | rw [submissionInstructionsChunk6_length]
    | rw [submissionInstructionsChunk7_length]
    | rw [submissionInstructionsChunk8_length]
    | rw [submissionInstructionsChunk9_length]
    | rw [submissionInstructionsChunk10_length]
    | rw [submissionInstructionsChunk11_length]
    | rw [submissionInstructionsChunk12_length]
    | rw [submissionInstructionsChunk13_length]
    | rw [submissionInstructionsChunk14_length]
    | rw [submissionInstructionsChunk16]
    | rfl)

private theorem dispatchSuffix_bytes :
    (YulEvmCompiler.assembleBytes dispatchSuffix).length = 33 := by
  rw [dispatchSuffix_eq]
  rfl

private theorem artifact_dispatch_split :
    Artifact.submissionInstructions = dispatchPrefix ++ dispatchSuffix := by
  simp only [dispatchPrefix, dispatchSuffix, List.take_append_drop]

private theorem artifact_dispatch_split3 :
    Artifact.submissionArtifact.instructions =
      dispatchPrefix ++ dispatchSuffix ++ [] := by
  change Artifact.submissionInstructions = dispatchPrefix ++ dispatchSuffix ++ []
  rw [artifact_dispatch_split, List.append_nil]

private theorem dispatch_instr (i : Nat) (hi : i < dispatchSuffix.length) :
    Artifact.submissionArtifact.instructions[2872 + i]? = dispatchSuffix[i]? := by
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 i hi
  simpa [dispatchPrefix_length] using h

private theorem opByte_eq (opcode : UInt8) {op : Operation}
    (h : Decode.opcodeOf opcode = some op) :
    Artifact.op opcode = .op op := by
  simp [Artifact.op, h]

private theorem dispatch_instr_2872 :
    Artifact.submissionArtifact.instructions[2872]? = some (.op .JUMPDEST) := by
  have h := dispatch_instr 0 (by simp [dispatchSuffix_length])
  have hop : Artifact.op 0x5b = .op .JUMPDEST := opByte_eq 0x5b (by decide)
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15, hop] using h

private theorem dispatch_instr_2873 :
    Artifact.submissionArtifact.instructions[2873]? = some (.op .CALLDATASIZE) := by
  have h := dispatch_instr 1 (by simp [dispatchSuffix_length])
  have hop : Artifact.op 0x36 = .op .CALLDATASIZE := opByte_eq 0x36 (by decide)
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15, hop] using h

private theorem dispatch_instr_2874 :
    Artifact.submissionArtifact.instructions[2874]? =
      some (.push 2 1006) := by
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15] using dispatch_instr 2 (by simp [dispatchSuffix_length])

private theorem dispatch_instr_2875 :
    Artifact.submissionArtifact.instructions[2875]? = some (.op .JUMPI) := by
  have h := dispatch_instr 3 (by simp [dispatchSuffix_length])
  have hop : Artifact.op 0x57 = .op .JUMPI := opByte_eq 0x57 (by decide)
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15, hop] using h

private theorem dispatch_instr_2876 :
    Artifact.submissionArtifact.instructions[2876]? =
      some (.push 20 0x9c1185a5c5e9fc54612808977ee8f548b2258d31) := by
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15] using dispatch_instr 4 (by simp [dispatchSuffix_length])

private theorem dispatch_instr_2877 :
    Artifact.submissionArtifact.instructions[2877]? = some (.push 0 0) := by
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15] using dispatch_instr 5 (by simp [dispatchSuffix_length])

private theorem dispatch_instr_2878 :
    Artifact.submissionArtifact.instructions[2878]? = some (.op .MSTORE) := by
  have h := dispatch_instr 6 (by simp [dispatchSuffix_length])
  have hop : Artifact.op 0x52 = .op .MSTORE := opByte_eq 0x52 (by decide)
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15, hop] using h

private theorem dispatch_instr_2879 :
    Artifact.submissionArtifact.instructions[2879]? = some (.push 1 32) := by
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15] using dispatch_instr 7 (by simp [dispatchSuffix_length])

private theorem dispatch_instr_2880 :
    Artifact.submissionArtifact.instructions[2880]? = some (.push 0 0) := by
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15] using dispatch_instr 8 (by simp [dispatchSuffix_length])

private theorem dispatch_instr_2881 :
    Artifact.submissionArtifact.instructions[2881]? = some (.op .RETURN) := by
  have h := dispatch_instr 9 (by simp [dispatchSuffix_length])
  have hop : Artifact.op 0xf3 = .op .RETURN := opByte_eq 0xf3 (by decide)
  simpa [dispatchSuffix_eq, submissionInstructionsChunk15, hop] using h

private theorem dispatch_code_bytes :
    (YulEvmCompiler.assembleBytes Artifact.submissionInstructions).length = 4955 := by
  have h := congrArg ByteArray.size Artifact.submissionArtifact.assembly_eq
  change (YulEvmCompiler.assembleBytes Artifact.submissionInstructions).toArray.size =
    Artifact.submissionArtifact.code.size at h
  have hsize : Artifact.submissionArtifact.code.size = 4955 := by
    change Challenge.Ripemd160.submissionBytecode.size = 4955
    exact Challenge.Ripemd160.referenceBytecode_size
  simpa only [List.size_toArray, hsize] using h

private theorem dispatch_prefix_bytes :
    (YulEvmCompiler.assembleBytes dispatchPrefix).length = 0x133a := by
  have hbytes : YulEvmCompiler.assembleBytes Artifact.submissionInstructions =
      YulEvmCompiler.assembleBytes dispatchPrefix ++
        YulEvmCompiler.assembleBytes dispatchSuffix := by
    rw [artifact_dispatch_split, YulEvmCompiler.assembleBytes_append]
  have hlen := congrArg List.length hbytes
  simp only [List.length_append, dispatchSuffix_bytes, dispatch_code_bytes] at hlen
  omega

private theorem dispatch_pc_base :
    Artifact.submissionArtifact.instructionPC 2872 = 0x133a := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 0
    (by simp [dispatchSuffix_length])
  rw [dispatchPrefix_length] at hseg
  have hnil : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 0)).length = 0 := rfl
  rw [hnil, Nat.add_zero, dispatch_prefix_bytes] at hseg
  exact hseg

section DispatchPCs

set_option maxRecDepth 50000

@[simp] theorem pc_dispatch_2872 :
    Artifact.submissionArtifact.instructionPC 2872 = 0x133a :=
  dispatch_pc_base

@[simp] theorem pc_dispatch_2873 :
    Artifact.submissionArtifact.instructionPC 2873 = 0x133b := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 1
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 1)).length = 1 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2874 :
    Artifact.submissionArtifact.instructionPC 2874 = 0x133c := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 2
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 2)).length = 2 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2875 :
    Artifact.submissionArtifact.instructionPC 2875 = 0x133f := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 3
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 3)).length = 5 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2876 :
    Artifact.submissionArtifact.instructionPC 2876 = 0x1340 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 4
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 4)).length = 6 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2877 :
    Artifact.submissionArtifact.instructionPC 2877 = 0x1355 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 5
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 5)).length = 27 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2878 :
    Artifact.submissionArtifact.instructionPC 2878 = 0x1356 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 6
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 6)).length = 28 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2879 :
    Artifact.submissionArtifact.instructionPC 2879 = 0x1357 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 7
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 7)).length = 29 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2880 :
    Artifact.submissionArtifact.instructionPC 2880 = 0x1359 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 8
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 8)).length = 31 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2881 :
    Artifact.submissionArtifact.instructionPC 2881 = 0x135a := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 9
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 9)).length = 32 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

end DispatchPCs

def path_start : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨0, .push ⟨2, by decide⟩ (UInt256.ofNat 0x133a), by rfl, by decide⟩,
   ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1b : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨20, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨21, .push ⟨2, by decide⟩ (UInt256.ofNat 0x2e), by rfl, by decide⟩,
   ⟨22, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_2e : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨35, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨36, .push ⟨2, by decide⟩ (UInt256.ofNat 0x46), by rfl, by decide⟩,
   ⟨37, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_46 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨52, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨53, .push ⟨2, by decide⟩ (UInt256.ofNat 0x5a), by rfl, by decide⟩,
   ⟨54, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_5a : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨67, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨68, .push ⟨2, by decide⟩ (UInt256.ofNat 0x73), by rfl, by decide⟩,
   ⟨69, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_73 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨83, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨84, .push ⟨2, by decide⟩ (UInt256.ofNat 0x8e), by rfl, by decide⟩,
   ⟨85, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_8e : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨105, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨106, .push ⟨2, by decide⟩ (UInt256.ofNat 0x10f), by rfl, by decide⟩,
   ⟨107, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_10f : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨205, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨206, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1b2), by rfl, by decide⟩,
   ⟨207, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1b2 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨313, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨314, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1db), by rfl, by decide⟩,
   ⟨315, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_1db : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨346, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨347, .push ⟨2, by decide⟩ (UInt256.ofNat 0x231), by rfl, by decide⟩,
   ⟨348, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_231 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨410, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨411, .push ⟨2, by decide⟩ (UInt256.ofNat 0x268), by rfl, by decide⟩,
   ⟨412, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_268 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨448, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨449, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3c1), by rfl, by decide⟩,
   ⟨450, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_3c1 : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨647, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨648, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3ee), by rfl, by decide⟩,
   ⟨649, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_3ee : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨682, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Dispatcher prefix: `JUMPDEST CALLDATASIZE PUSH2 0x3ee JUMPI`.
On the nonempty route `JUMPI` is taken to `0x3ee` with an empty stack. -/
def path_dispatch : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨2872, .op .JUMPDEST, dispatch_instr_2872, wfOp (by decide) trivial rfl⟩,
   ⟨2873, .op .CALLDATASIZE, dispatch_instr_2873, wfOp (by decide) trivial rfl⟩,
   ⟨2874, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3ee), dispatch_instr_2874, by decide⟩,
   ⟨2875, .op .JUMPI, dispatch_instr_2875, wfOp (by decide) trivial rfl⟩]

/-- 20-byte RIPEMD-160 digest of the empty input, returned by the
empty-dispatch fall-through. -/
def emptyDigestNat : Nat :=
  0x9c1185a5c5e9fc54612808977ee8f548b2258d31

/-- Empty fall-through tail: `PUSH20 digest PUSH0 MSTORE PUSH1 32 PUSH0 RETURN`
(indices `2876..2881`). -/
def path_empty_tail : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨2876, .push ⟨20, by decide⟩ (UInt256.ofNat emptyDigestNat), dispatch_instr_2876, by decide⟩,
   ⟨2877, .push ⟨0, by decide⟩ (UInt256.ofNat 0), dispatch_instr_2877, by decide⟩,
   ⟨2878, .op .MSTORE, dispatch_instr_2878, wfOp (by decide) trivial rfl⟩,
   ⟨2879, .push ⟨1, by decide⟩ (UInt256.ofNat 32), dispatch_instr_2879, by decide⟩,
   ⟨2880, .push ⟨0, by decide⟩ (UInt256.ofNat 0), dispatch_instr_2880, by decide⟩,
   ⟨2881, .op .RETURN, dispatch_instr_2881, wfOp (by decide) trivial rfl⟩]

/-- Full empty-dispatch path from the dispatcher entry through `RETURN`
(indices `2872..2881`). -/
def path_empty : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  path_dispatch ++ path_empty_tail

@[simp] theorem atPC_stack (input : ByteArray) (pc : Nat) :
    (atPC input pc).stack = [] := by rfl

@[simp] theorem atPC_calldata (input : ByteArray) (pc : Nat) :
    (atPC input pc).executionEnv.calldata = input := by rfl

@[simp] theorem atPC_code (input : ByteArray) (pc : Nat) :
    (atPC input pc).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem atPC_memory (input : ByteArray) (pc : Nat) :
    (atPC input pc).memory = (initialState submissionBytecode input 0).memory := by
  rfl

private theorem empty_entry_jumpdest :
    Decode.isValidJumpDest submissionBytecode 0x133a = true := by
  have hcode : Artifact.submissionArtifact.code = submissionBytecode := rfl
  have h := Artifact.submissionArtifact.isValidJumpDest_index 2872 dispatch_instr_2872
  simpa only [hcode, pc_dispatch_2872] using h

def gasSteps_start (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0) (atPC input 0x133a) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x133a = true :=
    empty_entry_jumpdest
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_start
      (atPC input 0) = some (atPC input 0x133a) := by
    simp [path_start, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState, hdest]
  have g : Challenge.EvmProof.GasSteps (atPC input 0) (atPC input 0x133a) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka path_start
    · rfl
    · rfl
    · exact hrun
    · rfl
    · exact deployAddress_not_precompile
  exact Challenge.EvmProof.GasSteps.cast g rfl rfl

def gasSteps_1b (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b) (atPC input 0x2e) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1b
      (atPC input 0x1b) = some (atPC input 0x2e) := by
    simp [path_1b, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_1b
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_2e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x2e) (atPC input 0x46) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_2e
      (atPC input 0x2e) = some (atPC input 0x46) := by
    simp [path_2e, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_2e
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_46 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x46) (atPC input 0x5a) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_46
      (atPC input 0x46) = some (atPC input 0x5a) := by
    simp [path_46, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_46
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_5a (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x5a) (atPC input 0x73) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_5a
      (atPC input 0x5a) = some (atPC input 0x73) := by
    simp [path_5a, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_5a
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_73 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x73) (atPC input 0x8e) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_73
      (atPC input 0x73) = some (atPC input 0x8e) := by
    simp [path_73, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_73
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_8e (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x8e) (atPC input 0x10f) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_8e
      (atPC input 0x8e) = some (atPC input 0x10f) := by
    simp [path_8e, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_8e
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_10f (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x10f) (atPC input 0x1b2) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_10f
      (atPC input 0x10f) = some (atPC input 0x1b2) := by
    simp [path_10f, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_10f
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_1b2 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1b2) (atPC input 0x1db) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1b2
      (atPC input 0x1b2) = some (atPC input 0x1db) := by
    simp [path_1b2, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_1b2
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_1db (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x1db) (atPC input 0x231) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_1db
      (atPC input 0x1db) = some (atPC input 0x231) := by
    simp [path_1db, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_1db
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_231 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x231) (atPC input 0x268) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_231
      (atPC input 0x231) = some (atPC input 0x268) := by
    simp [path_231, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_231
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_268 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x268) (atPC input 0x3c1) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_268
      (atPC input 0x268) = some (atPC input 0x3c1) := by
    simp [path_268, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_268
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_3c1 (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3c1) (atPC input 0x3ee) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_3c1
      (atPC input 0x3c1) = some (atPC input 0x3ee) := by
    simp [path_3c1, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_3c1
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_3ee (input : ByteArray) :
    Challenge.EvmProof.GasSteps (atPC input 0x3ee) (mainStart input) := by
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_3ee
      (atPC input 0x3ee) = some (mainStart input) := by
    simp [path_3ee, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, mainStart, initialState]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_3ee
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_dispatch_nonempty (input : ByteArray) (hfit : CalldataFits input)
    (hnonempty : input.size ≠ 0) :
    Challenge.EvmProof.GasSteps (atPC input 0x133a) (atPC input 0x3ee) := by
  have hbound : input.size < 2 ^ 256 := by
    unfold CalldataFits at hfit
    exact lt_trans hfit (by norm_num)
  have htrue : UInt256.isTrue (UInt256.ofNat input.size) := by
    unfold UInt256.isTrue
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbound]
    exact hnonempty
  have hdest : Decode.isValidJumpDest submissionBytecode 0x3ee = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_dispatch
      (atPC input 0x133a) = some (atPC input 0x3ee) := by
    simp [path_dispatch, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState, htrue, hdest]
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path_dispatch
  · rfl
  · rfl
  · exact hrun
  · rfl
  · exact deployAddress_not_precompile

def gasSteps_entry (input : ByteArray) (hfit : CalldataFits input)
    (hnonempty : input.size ≠ 0) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (mainStart input) :=
  (gasSteps_start input).trans
    ((gasSteps_dispatch_nonempty input hfit hnonempty).trans (gasSteps_3ee input))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
