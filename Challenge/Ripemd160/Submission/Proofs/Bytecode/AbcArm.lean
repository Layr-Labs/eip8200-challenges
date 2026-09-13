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

@[simp] theorem pc_176 : Artifact.submissionArtifact.instructionPC 238 = 351 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_241 : Artifact.submissionArtifact.instructionPC 3873 = 4966 := by
  exact GuardInstructionWindow.pc 222
@[simp] theorem pc_242 : Artifact.submissionArtifact.instructionPC 3874 = 4967 := by
  exact GuardInstructionWindow.pc 223
@[simp] theorem pc_243 : Artifact.submissionArtifact.instructionPC 3875 = 4968 := by
  exact GuardInstructionWindow.pc 224
@[simp] theorem pc_244 : Artifact.submissionArtifact.instructionPC 3876 = 4969 := by
  exact GuardInstructionWindow.pc 225
@[simp] theorem pc_245 : Artifact.submissionArtifact.instructionPC 3877 = 4970 := by
  exact GuardInstructionWindow.pc 226
@[simp] theorem pc_4089 : Artifact.submissionArtifact.instructionPC 3852 = 4896 := by
  exact GuardInstructionWindow.pc 201
@[simp] theorem pc_4090 : Artifact.submissionArtifact.instructionPC 3853 = 4897 := by
  exact GuardInstructionWindow.pc 202
@[simp] theorem pc_4091 : Artifact.submissionArtifact.instructionPC 3854 = 4898 := by
  exact GuardInstructionWindow.pc 203
@[simp] theorem pc_4092 : Artifact.submissionArtifact.instructionPC 3855 = 4900 := by
  exact GuardInstructionWindow.pc 204
@[simp] theorem pc_4093 : Artifact.submissionArtifact.instructionPC 3856 = 4901 := by
  exact GuardInstructionWindow.pc 205
@[simp] theorem pc_4094 : Artifact.submissionArtifact.instructionPC 3857 = 4904 := by
  exact GuardInstructionWindow.pc 206
@[simp] theorem pc_4095 : Artifact.submissionArtifact.instructionPC 3858 = 4905 := by
  exact GuardInstructionWindow.pc 207
@[simp] theorem pc_4096 : Artifact.submissionArtifact.instructionPC 3859 = 4909 := by
  exact GuardInstructionWindow.pc 208
@[simp] theorem pc_4097 : Artifact.submissionArtifact.instructionPC 3860 = 4910 := by
  exact GuardInstructionWindow.pc 209
@[simp] theorem pc_4098 : Artifact.submissionArtifact.instructionPC 3861 = 4911 := by
  exact GuardInstructionWindow.pc 210
@[simp] theorem pc_4099 : Artifact.submissionArtifact.instructionPC 3862 = 4912 := by
  exact GuardInstructionWindow.pc 211
@[simp] theorem pc_4100 : Artifact.submissionArtifact.instructionPC 3863 = 4913 := by
  exact GuardInstructionWindow.pc 212
@[simp] theorem pc_4101 : Artifact.submissionArtifact.instructionPC 3864 = 4915 := by
  exact GuardInstructionWindow.pc 213
@[simp] theorem pc_4102 : Artifact.submissionArtifact.instructionPC 3865 = 4916 := by
  exact GuardInstructionWindow.pc 214
@[simp] theorem pc_4103 : Artifact.submissionArtifact.instructionPC 3866 = 4917 := by
  exact GuardInstructionWindow.pc 215
@[simp] theorem pc_4104 : Artifact.submissionArtifact.instructionPC 3867 = 4920 := by
  exact GuardInstructionWindow.pc 216
@[simp] theorem pc_4105 : Artifact.submissionArtifact.instructionPC 3868 = 4921 := by
  exact GuardInstructionWindow.pc 217
@[simp] theorem pc_4106 : Artifact.submissionArtifact.instructionPC 3869 = 4922 := by
  exact GuardInstructionWindow.pc 218
@[simp] theorem pc_4107 : Artifact.submissionArtifact.instructionPC 3870 = 4943 := by
  exact GuardInstructionWindow.pc 219
@[simp] theorem pc_4108 : Artifact.submissionArtifact.instructionPC 3871 = 4944 := by
  exact GuardInstructionWindow.pc 220
@[simp] theorem pc_4109 : Artifact.submissionArtifact.instructionPC 3872 = 4965 := by
  exact GuardInstructionWindow.pc 221

def sizePath : List Located :=
  [⟨3852, .op .JUMPDEST, by exact GuardInstructionWindow.get 201, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3853, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 202, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3854, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by exact GuardInstructionWindow.get 203, by decide⟩,
   ⟨3855, .op .SHR, by exact GuardInstructionWindow.get 204, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3856, .push ⟨2, by decide⟩ (UInt256.ofNat 351), by exact GuardInstructionWindow.get 205, by decide⟩,
   ⟨3857, .op .JUMPI, by exact GuardInstructionWindow.get 206, ⟨by decide, trivial, rfl⟩⟩]

def wordPath : List Located :=
  [⟨3858, .push ⟨3, by decide⟩ (UInt256.ofNat 2127393), by exact GuardInstructionWindow.get 207, by decide⟩,
   ⟨3859, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 208, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3860, .op .MUL, by exact GuardInstructionWindow.get 209, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3861, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 210, by decide⟩,
   ⟨3862, .op .CALLDATALOAD, by exact GuardInstructionWindow.get 211, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3863, .push ⟨1, by decide⟩ (UInt256.ofNat 232), by exact GuardInstructionWindow.get 212, by decide⟩,
   ⟨3864, .op .SHR, by exact GuardInstructionWindow.get 213, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3865, .op .XOR, by exact GuardInstructionWindow.get 214, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3866, .push ⟨2, by decide⟩ (UInt256.ofNat 351), by exact GuardInstructionWindow.get 215, by decide⟩,
   ⟨3867, .op .JUMPI, by exact GuardInstructionWindow.get 216, ⟨by decide, trivial, rfl⟩⟩]

/-- The small-input answer block sits at the end of the code and is entered by fall-through
from the word test. -/
def storePath : List Located :=
  [⟨3868, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 217, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3869, .push ⟨20, by decide⟩ (UInt256.ofNat 25448770637332498804579667936807160623886401639), by exact GuardInstructionWindow.get 218, by decide⟩,
   ⟨3870, .op .MUL, by exact GuardInstructionWindow.get 219, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3871, .push ⟨20, by decide⟩ (UInt256.ofNat 890993315260586290631548281360202943075753233713), by exact GuardInstructionWindow.get 220, by decide⟩,
   ⟨3872, .op .SUB, by exact GuardInstructionWindow.get 221, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3873, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 222, by decide⟩,
   ⟨3874, .op .MSTORE, by exact GuardInstructionWindow.get 223, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨3876, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 225, by decide⟩,
   ⟨3877, .op .RETURN, by exact GuardInstructionWindow.get 226, ⟨by decide, trivial, rfl⟩⟩]

def sizeCond (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2)
def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (leadWord input)
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621))
def armEntry (input : ByteArray) : State := Execution.atPC input 4896
def fallbackState (input : ByteArray) : State := Execution.atPC input 351
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
    pc := UInt256.ofNat 4968
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def sized (input : ByteArray) : State :=
  {stored input with pc := UInt256.ofNat 4969, stack := [UInt256.ofNat 32]}
def returned (input : ByteArray) : State :=
  {stored input with
    pc := UInt256.ofNat 4970
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

theorem arm_dest : Decode.isValidJumpDest submissionBytecode 4896 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3852 (by exact GuardInstructionWindow.get 201)
  rw [pc_4089] at h
  exact h
private theorem valid_generic : Decode.isValidJumpDest submissionBytecode 351 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 238 (by rfl)
  rw [pc_176] at h
  exact h
theorem run_large (input : ByteArray) (hm : sizeCond input ≠ 0) :
    DataStepper.runLocatedBlock sizePath (armEntry input) = some (fallbackState input) := by
  have ht := true_of_ne_zero (sizeCond input) hm
  simp [sizeCond] at ht
  simp [sizePath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    armEntry, fallbackState, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, ht, valid_generic]

theorem run_small (input : ByteArray) (hm : sizeCond input = 0) :
    DataStepper.runLocatedBlock sizePath (armEntry input) =
      some (Execution.atPC input 4905) := by
  have ht : ¬ UInt256.isTrue (sizeCond input) := by rw [hm]; decide
  simp [sizeCond] at ht
  simp [sizePath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    armEntry, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, ht]

theorem run_word_miss (input : ByteArray) (hm : wordCond input ≠ 0) :
    DataStepper.runLocatedBlock wordPath (Execution.atPC input 4905) =
      some (fallbackState input) := by
  have ht := true_of_ne_zero (wordCond input) hm
  simp [wordCond, leadWord] at ht
  simp [wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    fallbackState, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht, valid_generic]

theorem run_word_hit (input : ByteArray) (hm : wordCond input = 0) :
    DataStepper.runLocatedBlock wordPath (Execution.atPC input 4905) =
      some (Execution.atPC input 4921) := by
  have ht : ¬ UInt256.isTrue (wordCond input) := by rw [hm]; decide
  simp [wordCond, leadWord] at ht
  simp [wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht]

theorem run_store (input : ByteArray) :
    DataStepper.runLocatedBlock storePath (Execution.atPC input 4921) = some (stored input) := by
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

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hnabc : input ≠ AbcInputData.abcInput) :
    GasSteps (armEntry input) (fallbackState input) := by
  by_cases hs : sizeCond input = 0
  · have hw : wordCond input ≠ 0 := by
      intro hz
      have hc : condition input = 0 := by
        change UInt256.lor (wordCond input) (sizeCond input) = 0
        rw [hz, hs]
        decide
      rcases zero_cases input hfit hc with he | ha
      · have hn : input.size = 0 := by rw [he]; rfl
        omega
      · exact hnabc ha
    exact (sound sizePath (run_small input hs)).trans
      (sound wordPath (run_word_miss input hw))
  · exact sound sizePath (run_large input hs)

def gasSteps_hit (input : ByteArray) (hs : sizeCond input = 0) (hw : wordCond input = 0) :
    GasSteps (armEntry input) (returned input) := by
  have gd := sound sizePath (run_small input hs)
  have gw := sound wordPath (run_word_hit input hw)
  have gs := sound storePath (run_store input)
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3875 .MSIZE
    (by exact GuardInstructionWindow.get 224) (by decide) trivial
  have hp : (stored input).pc.toNat = Artifact.submissionArtifact.instructionPC 3875 := by
    rw [pc_243]; rfl
  have hop : (stored input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (stored input) 3875 rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  have gm : GasSteps (stored input) (sized input) := by
    simpa [stored, sized, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := sound finishPath (run_finish input)
  exact gd.trans (gw.trans (gs.trans (gm.trans gf)))

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
  let trace := entryPrefix.trans (gasSteps_hit input hs hw)
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
