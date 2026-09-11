import Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuardLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuard
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open TinyGuardLogic
abbrev Located := Stepper.Located Artifact.submissionArtifact .Osaka
@[simp] theorem pc_255 : Artifact.submissionArtifact.instructionPC 255 = 393 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_256 : Artifact.submissionArtifact.instructionPC 256 = 394 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_257 : Artifact.submissionArtifact.instructionPC 257 = 395 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_258 : Artifact.submissionArtifact.instructionPC 258 = 397 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_259 : Artifact.submissionArtifact.instructionPC 259 = 398 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_260 : Artifact.submissionArtifact.instructionPC 260 = 402 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_261 : Artifact.submissionArtifact.instructionPC 261 = 403 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_262 : Artifact.submissionArtifact.instructionPC 262 = 404 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_263 : Artifact.submissionArtifact.instructionPC 263 = 405 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_264 : Artifact.submissionArtifact.instructionPC 264 = 406 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_265 : Artifact.submissionArtifact.instructionPC 265 = 408 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_266 : Artifact.submissionArtifact.instructionPC 266 = 409 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_267 : Artifact.submissionArtifact.instructionPC 267 = 410 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_268 : Artifact.submissionArtifact.instructionPC 268 = 411 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_269 : Artifact.submissionArtifact.instructionPC 269 = 414 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_270 : Artifact.submissionArtifact.instructionPC 270 = 415 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_271 : Artifact.submissionArtifact.instructionPC 271 = 416 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_272 : Artifact.submissionArtifact.instructionPC 272 = 437 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_273 : Artifact.submissionArtifact.instructionPC 273 = 438 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_274 : Artifact.submissionArtifact.instructionPC 274 = 459 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_275 : Artifact.submissionArtifact.instructionPC 275 = 460 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_276 : Artifact.submissionArtifact.instructionPC 276 = 461 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_277 : Artifact.submissionArtifact.instructionPC 277 = 462 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_278 : Artifact.submissionArtifact.instructionPC 278 = 463 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_279 : Artifact.submissionArtifact.instructionPC 279 = 464 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_280 : Artifact.submissionArtifact.instructionPC 280 = 465 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def decisionPath : List Located :=
  [⟨255, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨256, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨257, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨258, .op .SHR, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨259, .push ⟨3, by decide⟩ (UInt256.ofNat 2127393), by rfl, by decide⟩,
   ⟨260, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨261, .op .MUL, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨262, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨263, .op .CALLDATALOAD, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨264, .push ⟨1, by decide⟩ (UInt256.ofNat 232), by rfl, by decide⟩,
   ⟨265, .op .SHR, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨266, .op .XOR, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨267, .op .OR, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨268, .push ⟨2, by decide⟩ (UInt256.ofNat 465), by rfl, by decide⟩,
   ⟨269, .op .JUMPI, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def storePath : List Located :=
  [⟨270, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨271, .push ⟨20, by decide⟩ (UInt256.ofNat 25448770637332498804579667936807160623886401639), by rfl, by decide⟩,
   ⟨272, .op .MUL, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨273, .push ⟨20, by decide⟩ (UInt256.ofNat 890993315260586290631548281360202943075753233713), by rfl, by decide⟩,
   ⟨274, .op .SUB, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨275, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨276, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨278, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨279, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def answerWord (input : ByteArray) : UInt256 :=
  UInt256.sub (UInt256.ofNat EmptySpec.digestNat)
    (UInt256.mul (UInt256.ofNat 25448770637332498804579667936807160623886401639)
      (UInt256.ofNat input.size))
def answerBytes (input : ByteArray) : ByteArray :=
  Data.Bytes.natToBytesPadded (answerWord input).toNat 32
def answerMemory (input : ByteArray) : ByteArray :=
  MachineState.writeBytes ByteArray.empty (answerBytes input) 0
def stored (input : ByteArray) : State :=
  {initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 462
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def sized (input : ByteArray) : State :=
  {stored input with pc := UInt256.ofNat 463, stack := [UInt256.ofNat 32]}
def returned (input : ByteArray) : State :=
  {stored input with
    pc := UInt256.ofNat 464
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory input) 0 32}

@[simp] private theorem add_nat (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b
@[simp] private theorem zero_toNat : ({val := 0} : UInt256).toNat = 0 := rfl
private theorem mul_op (a b : UInt256) : a * b = UInt256.mul a b := rfl
@[simp] private theorem literal_zero_toNat : (0 : UInt256).toNat = 0 := rfl
private theorem sub_op (a b : UInt256) : a - b = UInt256.sub a b := rfl

private theorem true_of_ne_zero (w : UInt256) (h : w ≠ 0) : UInt256.isTrue w = true := by
  have ht : UInt256.isTrue w := by
    intro hn
    apply h
    apply Word.word_ext
    exact hn
  simpa using ht

private theorem valid_generic : Decode.isValidJumpDest submissionBytecode 465 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 280 (by rfl)
  rw [pc_280] at h
  exact h

theorem run_miss (input : ByteArray) (hm : condition input ≠ 0) :
    Stepper.runLocatedBlock decisionPath (Execution.atPC input 393) =
      some (Execution.atPC input 465) := by
  have ht := true_of_ne_zero (condition input) hm
  simp [condition, leadWord] at ht
  simp [decisionPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Execution.atPC, initialState, UInt256.succ, Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht, valid_generic]

theorem run_hit (input : ByteArray) (hm : condition input = 0) :
    Stepper.runLocatedBlock decisionPath (Execution.atPC input 393) =
      some (Execution.atPC input 415) := by
  have ht : ¬ UInt256.isTrue (condition input) := by rw [hm]; decide
  simp [condition, leadWord] at ht
  simp [decisionPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Execution.atPC, initialState, UInt256.succ, Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht]

theorem run_store (input : ByteArray) :
    Stepper.runLocatedBlock storePath (Execution.atPC input 415) = some (stored input) := by
  simp [storePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Execution.atPC, initialState, stored, answerMemory, answerBytes, answerWord,
    EmptySpec.digestNat, UInt256.succ, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, Word.word_toNat_ofNat, Word.ofNat_add_mod, mul_op, sub_op, initialState]

theorem run_finish (input : ByteArray) :
    Stepper.runLocatedBlock finishPath (sized input) = some (returned input) := by
  simp [finishPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    sized, stored, returned, UInt256.succ, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, Word.word_toNat_ofNat, Word.ofNat_add_mod, mul_op, sub_op, initialState]

def gasSteps_miss (input : ByteArray) (hm : condition input ≠ 0) :
    GasSteps (Execution.atPC input 393) (Execution.atPC input 465) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka decisionPath
    rfl rfl (run_miss input hm) rfl deployAddress_not_precompile

def gasSteps_hit (input : ByteArray) (hm : condition input = 0) :
    GasSteps (Execution.atPC input 393) (returned input) := by
  have gd := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka decisionPath
    rfl rfl (run_hit input hm) rfl deployAddress_not_precompile
  have gs := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka storePath
    rfl rfl (run_store input) rfl deployAddress_not_precompile
  have hd := Artifact.submissionArtifact.decodeAt_op_index 277 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (stored input).pc.toNat = Artifact.submissionArtifact.instructionPC 277 := by
    rw [pc_277]; rfl
  have hop : (stored input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (stored input) 277
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  have gm : GasSteps (stored input) (sized input) := by
    simpa [stored, sized, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka finishPath
    rfl rfl (run_finish input) rfl deployAddress_not_precompile
  exact gd.trans (gs.trans (gm.trans gf))

theorem answer_empty : answerBytes ByteArray.empty = EmptySpec.emptyOutput := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide
theorem answer_abc : answerBytes TinyABCSpec.inputBytes = TinyABCSpec.abcOutput := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide

theorem correct_hit (input : ByteArray) (hfit : CalldataFits input) (hm : condition input = 0)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 393)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_hit input hm)
  have hspec : spec input = answerBytes input := by
    rcases zero_cases input hfit hm with h | h
    · subst input; rw [EmptySpec.spec_empty, answer_empty]
    · subst input; rw [TinyABCSpec.spec_abc, answer_abc]
  have hsize : (answerBytes input).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have hread : MachineState.readPadded (answerMemory input) 0 32 = answerBytes input := by
    rw [← hsize]
    exact Memory.readPadded_writeBytes_same ByteArray.empty (answerBytes input) 0
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, returned, stored, State.isDone, State.isHalted, State.isRunning]
    rfl)
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (MachineState.readPadded (answerMemory input) 0 32)) at heval
  rw [hread, ← hspec] at heval
  exact heval
#print axioms correct_hit
#print axioms gasSteps_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuard
