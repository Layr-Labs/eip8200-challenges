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

/-! ## H35 dispatcher PCs (frozen 5299-byte / 2171-instruction artifact).

The new tail appends ten instructions at `0x1492` (indices `2161..2170`).
Bounds use the 33-byte suffix certificate; no whole-prefix `decide` over
2161+ instructions. Fixed bytes preserved. -/

open private
  submissionInstructionsChunk0 submissionInstructionsChunk1
  submissionInstructionsChunk2 submissionInstructionsChunk3
  submissionInstructionsChunk4 submissionInstructionsChunk5
  submissionInstructionsChunk6 submissionInstructionsChunk7
  submissionInstructionsChunk8 submissionInstructionsChunk9
  submissionInstructionsChunk10
  submissionInstructionsChunk0_length submissionInstructionsChunk1_length
  submissionInstructionsChunk2_length submissionInstructionsChunk3_length
  submissionInstructionsChunk4_length submissionInstructionsChunk5_length
  submissionInstructionsChunk6_length submissionInstructionsChunk7_length
  submissionInstructionsChunk8_length submissionInstructionsChunk9_length
  submissionInstructionsChunk10_length
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

private def dispatchPrefix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0 ++ submissionInstructionsChunk1 ++
    submissionInstructionsChunk2 ++ submissionInstructionsChunk3 ++
    submissionInstructionsChunk4 ++ submissionInstructionsChunk5 ++
    submissionInstructionsChunk6 ++ submissionInstructionsChunk7 ++
    submissionInstructionsChunk8 ++ submissionInstructionsChunk9 ++
    submissionInstructionsChunk10.take 221

private def dispatchSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk10.drop 221

private theorem dispatchPrefix_length : dispatchPrefix.length = 2161 := by
  simp [dispatchPrefix]

private theorem dispatchSuffix_length : dispatchSuffix.length = 10 := by
  simp [dispatchSuffix]

private theorem dispatchSuffix_bytes :
    (YulEvmCompiler.assembleBytes dispatchSuffix).length = 33 := by
  rfl

private theorem artifact_dispatch_split :
    Artifact.submissionInstructions = dispatchPrefix ++ dispatchSuffix := by
  simp only [Artifact.submissionInstructions, dispatchPrefix, dispatchSuffix,
    List.append_assoc, List.take_append_drop]

private theorem artifact_dispatch_split3 :
    Artifact.submissionArtifact.instructions =
      dispatchPrefix ++ dispatchSuffix ++ [] := by
  change Artifact.submissionInstructions = dispatchPrefix ++ dispatchSuffix ++ []
  rw [artifact_dispatch_split]
  simp

private theorem dispatch_code_bytes :
    (YulEvmCompiler.assembleBytes Artifact.submissionInstructions).length = 5299 := by
  have h := congrArg ByteArray.size Artifact.submissionArtifact.assembly_eq
  change (YulEvmCompiler.assembleBytes Artifact.submissionInstructions).toArray.size =
    Artifact.submissionArtifact.code.size at h
  have hsize : Artifact.submissionArtifact.code.size = 5299 := by
    change Challenge.Ripemd160.submissionBytecode.size = 5299
    exact Challenge.Ripemd160.referenceBytecode_size
  simpa only [List.size_toArray, hsize] using h

private theorem dispatch_prefix_bytes :
    (YulEvmCompiler.assembleBytes dispatchPrefix).length = 0x1492 := by
  have hbytes : YulEvmCompiler.assembleBytes Artifact.submissionInstructions =
      YulEvmCompiler.assembleBytes dispatchPrefix ++
        YulEvmCompiler.assembleBytes dispatchSuffix := by
    rw [artifact_dispatch_split, YulEvmCompiler.assembleBytes_append]
  have hlen := congrArg List.length hbytes
  simp only [List.length_append, dispatchSuffix_bytes, dispatch_code_bytes] at hlen
  omega

private theorem dispatch_pc_base :
    Artifact.submissionArtifact.instructionPC 2161 = 0x1492 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 0
    (by simp [dispatchSuffix_length])
  simpa [dispatchPrefix_length, dispatch_prefix_bytes] using hseg

section DispatchPCs

set_option maxRecDepth 50000

@[simp] theorem pc_dispatch_2161 :
    Artifact.submissionArtifact.instructionPC 2161 = 0x1492 :=
  dispatch_pc_base

@[simp] theorem pc_dispatch_2162 :
    Artifact.submissionArtifact.instructionPC 2162 = 0x1493 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 1
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 1)).length = 1 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2163 :
    Artifact.submissionArtifact.instructionPC 2163 = 0x1494 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 2
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 2)).length = 2 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2164 :
    Artifact.submissionArtifact.instructionPC 2164 = 0x1497 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 3
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 3)).length = 5 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2165 :
    Artifact.submissionArtifact.instructionPC 2165 = 0x1498 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 4
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 4)).length = 6 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2166 :
    Artifact.submissionArtifact.instructionPC 2166 = 0x14ad := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 5
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 5)).length = 27 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2167 :
    Artifact.submissionArtifact.instructionPC 2167 = 0x14ae := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 6
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 6)).length = 28 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2168 :
    Artifact.submissionArtifact.instructionPC 2168 = 0x14af := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 7
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 7)).length = 29 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2169 :
    Artifact.submissionArtifact.instructionPC 2169 = 0x14b1 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 8
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 8)).length = 31 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

@[simp] theorem pc_dispatch_2170 :
    Artifact.submissionArtifact.instructionPC 2170 = 0x14b2 := by
  have hseg := ArtifactSegment.instructionPC_segment Artifact.submissionArtifact
    dispatchPrefix dispatchSuffix [] artifact_dispatch_split3 9
    (by simp [dispatchSuffix_length])
  have htake : (YulEvmCompiler.assembleBytes (dispatchSuffix.take 9)).length = 32 := by
    rfl
  rw [dispatchPrefix_length, htake, dispatch_prefix_bytes] at hseg
  norm_num at hseg
  exact hseg

end DispatchPCs

/-- Entry now jumps to the appended dispatcher, not directly to `0x3ee`. -/
def path_start : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨0, .push ⟨2, by decide⟩ (UInt256.ofNat 0x1492), by rfl, by decide⟩,
   ⟨1, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def path_3ee : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨682, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Dispatcher prefix: `JUMPDEST CALLDATASIZE PUSH2 0x3ee JUMPI`.
On the nonempty route `JUMPI` is taken to `0x3ee` with an empty stack. -/
def path_dispatch : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨2161, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2162, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2163, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3ee), by rfl, by decide⟩,
   ⟨2164, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

/-- 20-byte RIPEMD-160 digest of the empty input, returned by the
empty-dispatch fall-through. -/
def emptyDigestNat : Nat :=
  0x9c1185a5c5e9fc54612808977ee8f548b2258d31

/-- Empty fall-through tail: `PUSH20 digest PUSH0 MSTORE PUSH1 32 PUSH0 RETURN`
(indices `2165..2170`). Provided for the next owner handling the final
empty/nonempty split; this file only certifies the nonempty prefix above. -/
def path_empty_tail : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨2165, .push ⟨20, by decide⟩ (UInt256.ofNat emptyDigestNat), by rfl, by decide⟩,
   ⟨2166, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨2167, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨2168, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨2169, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨2170, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Full empty-dispatch path from the dispatcher entry through `RETURN`
(indices `2161..2170`). The fall-through `JUMPI` (not taken) lands at
`0x1498`; the nonempty certificate below uses the taken branch instead. -/
def path_empty : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  path_dispatch ++ path_empty_tail

/-! ## Dispatcher context preservation on the nonempty route.

Both endpoints are `atPC` states over the same `input`, so execution context
(`executionEnv`, memory, `activeWords`, etc.) is definitionally preserved and
the stack is empty on arrival at `0x3ee`. These facts are stated explicitly
for the next owner and for gas accounting. -/

@[simp] theorem atPC_stack (input : ByteArray) (pc : Nat) :
    (atPC input pc).stack = [] := by rfl

@[simp] theorem atPC_calldata (input : ByteArray) (pc : Nat) :
    (atPC input pc).executionEnv.calldata = input := by rfl

@[simp] theorem atPC_code (input : ByteArray) (pc : Nat) :
    (atPC input pc).executionEnv.code = submissionBytecode := by rfl

@[simp] theorem atPC_memory (input : ByteArray) (pc : Nat) :
    (atPC input pc).memory = (initialState submissionBytecode input 0).memory := by
  rfl

theorem dispatch_endpoints_executionEnv (input : ByteArray) :
    (atPC input 0x3ee).executionEnv = (atPC input 0x1492).executionEnv := by
  rfl

theorem dispatch_endpoints_memory (input : ByteArray) :
    (atPC input 0x3ee).memory = (atPC input 0x1492).memory := by
  rfl

theorem dispatch_endpoints_activeWords (input : ByteArray) :
    (atPC input 0x3ee).activeWords = (atPC input 0x1492).activeWords := by
  rfl

theorem dispatch_target_stack_empty (input : ByteArray) :
    (atPC input 0x3ee).stack = [] := by
  rfl

theorem dispatch_target_halt_running (input : ByteArray) :
    (atPC input 0x3ee).halt = .Running := by
  rfl

def gasSteps_start (input : ByteArray) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0) (atPC input 0x1492) := by
  have hcode : Artifact.submissionArtifact.code = submissionBytecode := rfl
  have hdest : Decode.isValidJumpDest submissionBytecode 0x1492 = true := by
    have h := Artifact.submissionArtifact.isValidJumpDest_index 2161 (by rfl)
    simpa only [hcode, pc_dispatch_2161] using h
  have hrun : Challenge.EvmProof.Stepper.runLocatedBlock path_start
      (atPC input 0) = some (atPC input 0x1492) := by
    simp [path_start, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      atPC, initialState, hdest]
  have g : Challenge.EvmProof.GasSteps (atPC input 0) (atPC input 0x1492) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka path_start
    · rfl
    · rfl
    · exact hrun
    · rfl
    · exact deployAddress_not_precompile
  exact Challenge.EvmProof.GasSteps.cast g rfl rfl

def gasSteps_dispatch_nonempty (input : ByteArray) (hfit : CalldataFits input)
    (hnonempty : input.size ≠ 0) :
    Challenge.EvmProof.GasSteps (atPC input 0x1492) (atPC input 0x3ee) := by
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
      (atPC input 0x1492) = some (atPC input 0x3ee) := by
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

/-- Exact nonempty entry: unconditional start to the dispatcher, then the
taken `JUMPI` to `0x3ee` under `hfit`/`hnonempty`, then the `JUMPDEST` step
to `mainStart`. Models `mainStart`/`atPC` are unchanged. -/
def gasSteps_entry (input : ByteArray) (hfit : CalldataFits input)
    (hnonempty : input.size ≠ 0) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (mainStart input) :=
  (gasSteps_start input).trans
    ((gasSteps_dispatch_nonempty input hfit hnonempty).trans (gasSteps_3ee input))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
