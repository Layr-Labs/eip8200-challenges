import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GuardInstructionWindow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuardLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open TinyGuardLogic
abbrev Located := DataStepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem pc_176 : Artifact.submissionArtifact.instructionPC 245 = 357 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_241 : Artifact.submissionArtifact.instructionPC 3779 = 4948 := by
  exact GuardInstructionWindow.pc 216
@[simp] theorem pc_242 : Artifact.submissionArtifact.instructionPC 3780 = 4949 := by
  exact GuardInstructionWindow.pc 217
@[simp] theorem pc_243 : Artifact.submissionArtifact.instructionPC 3781 = 4950 := by
  exact GuardInstructionWindow.pc 218
@[simp] theorem pc_244 : Artifact.submissionArtifact.instructionPC 3782 = 4951 := by
  exact GuardInstructionWindow.pc 219
@[simp] theorem pc_245 : Artifact.submissionArtifact.instructionPC 3783 = 4952 := by
  exact GuardInstructionWindow.pc 220
@[simp] theorem pc_4095 : Artifact.submissionArtifact.instructionPC 3764 = 4887 := by
  exact GuardInstructionWindow.pc 201
@[simp] theorem pc_4096 : Artifact.submissionArtifact.instructionPC 3765 = 4888 := by
  exact GuardInstructionWindow.pc 202
@[simp] theorem pc_4097 : Artifact.submissionArtifact.instructionPC 3766 = 4889 := by
  exact GuardInstructionWindow.pc 203
@[simp] theorem pc_4098 : Artifact.submissionArtifact.instructionPC 3767 = 4891 := by
  exact GuardInstructionWindow.pc 204
@[simp] theorem pc_4099 : Artifact.submissionArtifact.instructionPC 3768 = 4892 := by
  exact GuardInstructionWindow.pc 205
@[simp] theorem pc_4100 : Artifact.submissionArtifact.instructionPC 3769 = 4893 := by
  exact GuardInstructionWindow.pc 206
@[simp] theorem pc_4101 : Artifact.submissionArtifact.instructionPC 3770 = 4897 := by
  exact GuardInstructionWindow.pc 207
@[simp] theorem pc_4102 : Artifact.submissionArtifact.instructionPC 3771 = 4898 := by
  exact GuardInstructionWindow.pc 208
@[simp] theorem pc_4103 : Artifact.submissionArtifact.instructionPC 3772 = 4899 := by
  exact GuardInstructionWindow.pc 209
@[simp] theorem pc_4104 : Artifact.submissionArtifact.instructionPC 3773 = 4902 := by
  exact GuardInstructionWindow.pc 210
@[simp] theorem pc_4105 : Artifact.submissionArtifact.instructionPC 3774 = 4903 := by
  exact GuardInstructionWindow.pc 211
@[simp] theorem pc_4106 : Artifact.submissionArtifact.instructionPC 3775 = 4924 := by
  exact GuardInstructionWindow.pc 212
@[simp] theorem pc_4107 : Artifact.submissionArtifact.instructionPC 3776 = 4925 := by
  exact GuardInstructionWindow.pc 213
@[simp] theorem pc_4108 : Artifact.submissionArtifact.instructionPC 3777 = 4926 := by
  exact GuardInstructionWindow.pc 214
@[simp] theorem pc_4109 : Artifact.submissionArtifact.instructionPC 3778 = 4947 := by
  exact GuardInstructionWindow.pc 215

def wordPath : List Located :=
  [⟨3764, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 201, by decide⟩,
   ⟨3765, .op .CALLDATALOAD, by exact GuardInstructionWindow.get 202, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3766, .push ⟨1, by decide⟩ (UInt256.ofNat 232), by exact GuardInstructionWindow.get 203, by decide⟩,
   ⟨3767, .op .SHR, by exact GuardInstructionWindow.get 204, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3768, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 205, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3769, .push ⟨3, by decide⟩ (UInt256.ofNat 2127393), by exact GuardInstructionWindow.get 206, by decide⟩,
   ⟨3770, .op .MUL, by exact GuardInstructionWindow.get 207, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3771, .op .XOR, by exact GuardInstructionWindow.get 208, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3772, .push ⟨2, by decide⟩ (UInt256.ofNat 357), by exact GuardInstructionWindow.get 209, by decide⟩,
   ⟨3773, .op .JUMPI, by exact GuardInstructionWindow.get 210, ⟨by decide, trivial, rfl⟩⟩]

/-- The small-input answer block sits at the end of the code and is entered by fall-through
from the word test. -/
def storePath : List Located :=
  [⟨3774, .push ⟨20, by decide⟩ (UInt256.ofNat 95383801997447390147238369573240532004699299169), by exact GuardInstructionWindow.get 211, by decide⟩,
   ⟨3775, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 212, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3776, .op .SHR, by exact GuardInstructionWindow.get 213, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3777, .push ⟨20, by decide⟩ (UInt256.ofNat 802931186561056611446976448233794645126013734992), by exact GuardInstructionWindow.get 214, by decide⟩,
   ⟨3778, .op .XOR, by exact GuardInstructionWindow.get 215, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3779, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 216, by decide⟩,
   ⟨3780, .op .MSTORE, by exact GuardInstructionWindow.get 217, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨3782, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 219, by decide⟩,
   ⟨3783, .op .RETURN, by exact GuardInstructionWindow.get 220, ⟨by decide, trivial, rfl⟩⟩]

def sizeCond (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2)
def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (leadWord input)
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621))
def armEntry (input : ByteArray) : State := Execution.atPC input 4887
def fallbackState (input : ByteArray) : State := Execution.atPC input 357
/-- The guarded sizes are zero and three. These constants reconstruct their
RIPEMD digests with a shift and XOR; the finite equalities are proved below. -/
def answerWord (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 802931186561056611446976448233794645126013734992)
    (UInt256.shiftRight (UInt256.ofNat 95383801997447390147238369573240532004699299169) (UInt256.ofNat input.size))
def answerBytes (input : ByteArray) : ByteArray :=
  Data.Bytes.natToBytesPadded (answerWord input).toNat 32
def answerMemory (input : ByteArray) : ByteArray :=
  MachineState.writeBytes ByteArray.empty (answerBytes input) 0
def stored (input : ByteArray) : State :=
  {initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4950
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def sized (input : ByteArray) : State :=
  {stored input with pc := UInt256.ofNat 4951, stack := [UInt256.ofNat 32]}
def returned (input : ByteArray) : State :=
  {stored input with
    pc := UInt256.ofNat 4952
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

private theorem valid_generic : Decode.isValidJumpDest submissionBytecode 357 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 245 (by rfl)
  rw [pc_176] at h
  exact h
theorem run_word_miss (input : ByteArray) (hm : wordCond input ≠ 0) :
    DataStepper.runLocatedBlock wordPath (armEntry input) =
      some (fallbackState input) := by
  have ht := true_of_ne_zero (wordCond input) hm
  simp [wordCond, leadWord, RawExpressionAC.mul_comm, RawExpressionAC.xor_comm] at ht
  simp [wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    armEntry, fallbackState, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, RawExpressionAC.mul_comm, RawExpressionAC.xor_comm, ht, valid_generic]

theorem run_word_hit (input : ByteArray) (hm : wordCond input = 0) :
    DataStepper.runLocatedBlock wordPath (armEntry input) =
      some (Execution.atPC input 4903) := by
  have ht : ¬ UInt256.isTrue (wordCond input) := by rw [hm]; decide
  simp [wordCond, leadWord, RawExpressionAC.mul_comm, RawExpressionAC.xor_comm] at ht
  simp [wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    armEntry, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, RawExpressionAC.mul_comm, RawExpressionAC.xor_comm, ht]

theorem run_store (input : ByteArray) :
    DataStepper.runLocatedBlock storePath (Execution.atPC input 4903) = some (stored input) := by
  simp [storePath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    Execution.atPC, initialState, stored, answerMemory, answerBytes, answerWord,
    EmptySpec.digestNat, UInt256.succ, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, Word.word_toNat_ofNat, Word.ofNat_add_mod,
    mul_op, sub_op, List.exchange, List.getElem?_cons_zero]

theorem run_finish (input : ByteArray) :
    DataStepper.runLocatedBlock finishPath (sized input) = some (returned input) := by
  simp [finishPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    sized, stored, returned, UInt256.succ, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, Word.word_toNat_ofNat, Word.ofNat_add_mod,
    mul_op, sub_op, initialState]

private def sound (path : List Located) {s t : State}
    (h : DataStepper.runLocatedBlock path s = some t)
    (hc : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hf : s.fork = .Osaka := by rfl) (hr : s.halt = .Running := by rfl)
    (hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by exact deployAddress_not_precompile) :
    GasSteps s t :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path hc hf h hr hn

def gasSteps_miss (input : ByteArray) (hw : wordCond input ≠ 0) :
    GasSteps (armEntry input) (fallbackState input) :=
  sound wordPath (run_word_miss input hw)

def gasSteps_hit (input : ByteArray) (hw : wordCond input = 0) :
    GasSteps (armEntry input) (returned input) := by
  have gw := sound wordPath (run_word_hit input hw)
  have gs := sound storePath (run_store input)
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3781 .MSIZE
    (by exact GuardInstructionWindow.get 218) (by decide) trivial
  have hp : (stored input).pc.toNat = Artifact.submissionArtifact.instructionPC 3781 := by
    rw [pc_243]; rfl
  have hop : (stored input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (stored input) 3781 rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  have gm : GasSteps (stored input) (sized input) := by
    simpa [stored, sized, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := sound finishPath (run_finish input)
  exact gw.trans (gs.trans (gm.trans gf))

theorem answer_empty : answerBytes ByteArray.empty = EmptySpec.emptyOutput := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide
theorem answer_abc : answerBytes AbcInputData.abcInput = AbcInputData.abcPaddedDigest := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide

theorem correct_hit (input : ByteArray) (hfit : CalldataFits input)
    (hs : sizeCond input = 0) (hw : wordCond input = 0)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_hit input hw)
  have hc : condition input = 0 := by
    change UInt256.lor (wordCond input) (sizeCond input) = 0
    rw [hw, hs]
    decide
  have hspec : spec input = answerBytes input := by
    rcases zero_cases input hfit hc with h | h
    · subst input; rw [EmptySpec.spec_empty, answer_empty]
    · subst input; rw [AbcDigest.spec_abc, answer_abc]
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

theorem correct_abc (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = AbcInputData.abcInput)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  have hc := condition_abc
  change UInt256.lor (wordCond AbcInputData.abcInput) (sizeCond AbcInputData.abcInput) = 0 at hc
  obtain ⟨hw, hs⟩ := (KnownInputLogic.wordOr_eq_zero_iff _ _).mp hc
  subst input
  exact correct_hit _ hfit hs hw entryPrefix

theorem correct_empty (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = ByteArray.empty)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  have hc := condition_empty
  change UInt256.lor (wordCond ByteArray.empty) (sizeCond ByteArray.empty) = 0 at hc
  obtain ⟨hw, hs⟩ := (KnownInputLogic.wordOr_eq_zero_iff _ _).mp hc
  subst input
  exact correct_hit _ hfit hs hw entryPrefix

#print axioms correct_hit
#print axioms gasSteps_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
