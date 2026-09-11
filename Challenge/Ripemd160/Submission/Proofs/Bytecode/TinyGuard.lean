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
@[simp] theorem pc_255 : Artifact.submissionArtifact.instructionPC 253 = 387 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_256 : Artifact.submissionArtifact.instructionPC 254 = 388 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_257 : Artifact.submissionArtifact.instructionPC 255 = 389 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_258 : Artifact.submissionArtifact.instructionPC 256 = 391 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_259 : Artifact.submissionArtifact.instructionPC 257 = 392 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_260 : Artifact.submissionArtifact.instructionPC 258 = 395 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_261 : Artifact.submissionArtifact.instructionPC 259 = 396 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_262 : Artifact.submissionArtifact.instructionPC 260 = 400 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_263 : Artifact.submissionArtifact.instructionPC 261 = 401 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_264 : Artifact.submissionArtifact.instructionPC 262 = 402 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_265 : Artifact.submissionArtifact.instructionPC 263 = 403 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_266 : Artifact.submissionArtifact.instructionPC 264 = 404 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_267 : Artifact.submissionArtifact.instructionPC 265 = 406 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_268 : Artifact.submissionArtifact.instructionPC 266 = 407 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_269 : Artifact.submissionArtifact.instructionPC 267 = 408 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_270 : Artifact.submissionArtifact.instructionPC 268 = 411 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_271 : Artifact.submissionArtifact.instructionPC 269 = 412 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_272 : Artifact.submissionArtifact.instructionPC 270 = 413 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_273 : Artifact.submissionArtifact.instructionPC 271 = 434 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_274 : Artifact.submissionArtifact.instructionPC 272 = 435 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_275 : Artifact.submissionArtifact.instructionPC 273 = 456 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_276 : Artifact.submissionArtifact.instructionPC 274 = 457 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_277 : Artifact.submissionArtifact.instructionPC 275 = 458 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_278 : Artifact.submissionArtifact.instructionPC 276 = 459 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_279 : Artifact.submissionArtifact.instructionPC 277 = 460 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_280 : Artifact.submissionArtifact.instructionPC 278 = 461 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_281 : Artifact.submissionArtifact.instructionPC 279 = 462 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def sizeWord (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2)
def mixWord (input : ByteArray) : UInt256 :=
  UInt256.xor (leadWord input) (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621))
theorem condition_split (input : ByteArray) :
    condition input = UInt256.lor (mixWord input) (sizeWord input) := rfl

def sizePath : List Located :=
  [⟨253, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨254, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨255, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨256, .op .SHR, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨257, .push ⟨2, by decide⟩ (UInt256.ofNat 462), by rfl, by decide⟩,
   ⟨258, .op .JUMPI, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def mixPath : List Located :=
  [⟨259, .push ⟨3, by decide⟩ (UInt256.ofNat 2127393), by rfl, by decide⟩,
   ⟨260, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨261, .op .MUL, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨262, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨263, .op .CALLDATALOAD, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨264, .push ⟨1, by decide⟩ (UInt256.ofNat 232), by rfl, by decide⟩,
   ⟨265, .op .SHR, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨266, .op .XOR, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨267, .push ⟨2, by decide⟩ (UInt256.ofNat 462), by rfl, by decide⟩,
   ⟨268, .op .JUMPI, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def storePath : List Located :=
  [⟨269, .op .CALLDATASIZE, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨270, .push ⟨20, by decide⟩ (UInt256.ofNat 25448770637332498804579667936807160623886401639), by rfl, by decide⟩,
   ⟨271, .op .MUL, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨272, .push ⟨20, by decide⟩ (UInt256.ofNat 890993315260586290631548281360202943075753233713), by rfl, by decide⟩,
   ⟨273, .op .SUB, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨274, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨275, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨277, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨278, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]

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
    pc := UInt256.ofNat 459
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def sized (input : ByteArray) : State :=
  {stored input with pc := UInt256.ofNat 460, stack := [UInt256.ofNat 32]}
def returned (input : ByteArray) : State :=
  {stored input with
    pc := UInt256.ofNat 461
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

private theorem valid_generic : Decode.isValidJumpDest submissionBytecode 462 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 279 (by rfl)
  rw [pc_281] at h
  exact h

theorem run_size_miss (input : ByteArray) (hm : sizeWord input ≠ 0) :
    Stepper.runLocatedBlock sizePath (Execution.atPC input 387) =
      some (Execution.atPC input 462) := by
  have ht := true_of_ne_zero (sizeWord input) hm
  simp [sizeWord] at ht
  simp [sizePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Execution.atPC, initialState, UInt256.succ, Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht, valid_generic]

theorem run_size_pass (input : ByteArray) (hm : sizeWord input = 0) :
    Stepper.runLocatedBlock sizePath (Execution.atPC input 387) =
      some (Execution.atPC input 396) := by
  have ht : ¬ UInt256.isTrue (sizeWord input) := by rw [hm]; decide
  simp [sizeWord] at ht
  simp [sizePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Execution.atPC, initialState, UInt256.succ, Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht]

theorem run_mix_miss (input : ByteArray) (hm : mixWord input ≠ 0) :
    Stepper.runLocatedBlock mixPath (Execution.atPC input 396) =
      some (Execution.atPC input 462) := by
  have ht := true_of_ne_zero (mixWord input) hm
  simp [mixWord, leadWord] at ht
  simp [mixPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Execution.atPC, initialState, UInt256.succ, Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht, valid_generic]

theorem run_mix_hit (input : ByteArray) (hm : mixWord input = 0) :
    Stepper.runLocatedBlock mixPath (Execution.atPC input 396) =
      some (Execution.atPC input 412) := by
  have ht : ¬ UInt256.isTrue (mixWord input) := by rw [hm]; decide
  simp [mixWord, leadWord] at ht
  simp [mixPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Execution.atPC, initialState, UInt256.succ, Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht]

theorem run_store (input : ByteArray) :
    Stepper.runLocatedBlock storePath (Execution.atPC input 412) = some (stored input) := by
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
    GasSteps (Execution.atPC input 387) (Execution.atPC input 462) :=
  if hs : sizeWord input = 0 then
    have hx : mixWord input ≠ 0 := fun hx =>
      hm ((KnownInputLogic.wordOr_eq_zero_iff (mixWord input) (sizeWord input)).mpr ⟨hx, hs⟩)
    (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka sizePath
      rfl rfl (run_size_pass input hs) rfl deployAddress_not_precompile).trans
    (Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka mixPath
      rfl rfl (run_mix_miss input hx) rfl deployAddress_not_precompile)
  else
    Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka sizePath
      rfl rfl (run_size_miss input hs) rfl deployAddress_not_precompile

def gasSteps_hit (input : ByteArray) (hm : condition input = 0) :
    GasSteps (Execution.atPC input 387) (returned input) := by
  have hz := (KnownInputLogic.wordOr_eq_zero_iff (mixWord input) (sizeWord input)).mp hm
  have g1 := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka sizePath
    rfl rfl (run_size_pass input hz.2) rfl deployAddress_not_precompile
  have g2 := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka mixPath
    rfl rfl (run_mix_hit input hz.1) rfl deployAddress_not_precompile
  have gs := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka storePath
    rfl rfl (run_store input) rfl deployAddress_not_precompile
  have hd := Artifact.submissionArtifact.decodeAt_op_index 276 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (stored input).pc.toNat = Artifact.submissionArtifact.instructionPC 276 := by
    rw [pc_278]; rfl
  have hop : (stored input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (stored input) 276
      rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  have gm : GasSteps (stored input) (sized input) := by
    simpa [stored, sized, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka finishPath
    rfl rfl (run_finish input) rfl deployAddress_not_precompile
  exact g1.trans (g2.trans (gs.trans (gm.trans gf)))

theorem answer_empty : answerBytes ByteArray.empty = EmptySpec.emptyOutput := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide
theorem answer_abc : answerBytes TinyABCSpec.inputBytes = TinyABCSpec.abcOutput := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide

theorem correct_hit (input : ByteArray) (hfit : CalldataFits input) (hm : condition input = 0)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 387)) :
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
