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
abbrev Located := Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem pc_176 : Artifact.submissionArtifact.instructionPC 230 = 335 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_236 : Artifact.submissionArtifact.instructionPC 275 = 417 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_237 : Artifact.submissionArtifact.instructionPC 276 = 418 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_238 : Artifact.submissionArtifact.instructionPC 277 = 440 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_239 : Artifact.submissionArtifact.instructionPC 278 = 441 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_240 : Artifact.submissionArtifact.instructionPC 279 = 442 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_241 : Artifact.submissionArtifact.instructionPC 280 = 443 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_242 : Artifact.submissionArtifact.instructionPC 281 = 444 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_243 : Artifact.submissionArtifact.instructionPC 282 = 445 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_244 : Artifact.submissionArtifact.instructionPC 283 = 446 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_245 : Artifact.submissionArtifact.instructionPC 284 = 447 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4089 : Artifact.submissionArtifact.instructionPC 3930 = 5151 := by
  exact GuardInstructionWindow.pc 155
@[simp] theorem pc_4090 : Artifact.submissionArtifact.instructionPC 3931 = 5152 := by
  exact GuardInstructionWindow.pc 156
@[simp] theorem pc_4091 : Artifact.submissionArtifact.instructionPC 3932 = 5153 := by
  exact GuardInstructionWindow.pc 157
@[simp] theorem pc_4092 : Artifact.submissionArtifact.instructionPC 3933 = 5155 := by
  exact GuardInstructionWindow.pc 158
@[simp] theorem pc_4093 : Artifact.submissionArtifact.instructionPC 3934 = 5156 := by
  exact GuardInstructionWindow.pc 159
@[simp] theorem pc_4094 : Artifact.submissionArtifact.instructionPC 3935 = 5159 := by
  exact GuardInstructionWindow.pc 160
@[simp] theorem pc_4095 : Artifact.submissionArtifact.instructionPC 3936 = 5160 := by
  exact GuardInstructionWindow.pc 161
@[simp] theorem pc_4096 : Artifact.submissionArtifact.instructionPC 3937 = 5164 := by
  exact GuardInstructionWindow.pc 162
@[simp] theorem pc_4097 : Artifact.submissionArtifact.instructionPC 3938 = 5165 := by
  exact GuardInstructionWindow.pc 163
@[simp] theorem pc_4098 : Artifact.submissionArtifact.instructionPC 3939 = 5166 := by
  exact GuardInstructionWindow.pc 164
@[simp] theorem pc_4099 : Artifact.submissionArtifact.instructionPC 3940 = 5167 := by
  exact GuardInstructionWindow.pc 165
@[simp] theorem pc_4100 : Artifact.submissionArtifact.instructionPC 3941 = 5168 := by
  exact GuardInstructionWindow.pc 166
@[simp] theorem pc_4101 : Artifact.submissionArtifact.instructionPC 3942 = 5170 := by
  exact GuardInstructionWindow.pc 167
@[simp] theorem pc_4102 : Artifact.submissionArtifact.instructionPC 3943 = 5171 := by
  exact GuardInstructionWindow.pc 168
@[simp] theorem pc_4103 : Artifact.submissionArtifact.instructionPC 3944 = 5172 := by
  exact GuardInstructionWindow.pc 169
@[simp] theorem pc_4104 : Artifact.submissionArtifact.instructionPC 3945 = 5175 := by
  exact GuardInstructionWindow.pc 170
@[simp] theorem pc_4105 : Artifact.submissionArtifact.instructionPC 3946 = 5176 := by
  exact GuardInstructionWindow.pc 171
@[simp] theorem pc_4106 : Artifact.submissionArtifact.instructionPC 3947 = 5197 := by
  exact GuardInstructionWindow.pc 172
@[simp] theorem pc_4107 : Artifact.submissionArtifact.instructionPC 3948 = 5198 := by
  exact GuardInstructionWindow.pc 173
@[simp] theorem pc_4108 : Artifact.submissionArtifact.instructionPC 3949 = 5201 := by
  exact GuardInstructionWindow.pc 174

def sizePath : List Located :=
  [⟨3930, .op .JUMPDEST, by exact GuardInstructionWindow.get 155, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3931, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 156, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3932, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by exact GuardInstructionWindow.get 157, by decide⟩,
   ⟨3933, .op .SHR, by exact GuardInstructionWindow.get 158, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3934, .push ⟨2, by decide⟩ (UInt256.ofNat 335), by exact GuardInstructionWindow.get 159, by decide⟩,
   ⟨3935, .op .JUMPI, by exact GuardInstructionWindow.get 160, ⟨by decide, trivial, rfl⟩⟩]

def wordPath : List Located :=
  [⟨3936, .push ⟨3, by decide⟩ (UInt256.ofNat 2127393), by exact GuardInstructionWindow.get 161, by decide⟩,
   ⟨3937, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 162, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3938, .op .MUL, by exact GuardInstructionWindow.get 163, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3939, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 164, by decide⟩,
   ⟨3940, .op .CALLDATALOAD, by exact GuardInstructionWindow.get 165, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3941, .push ⟨1, by decide⟩ (UInt256.ofNat 232), by exact GuardInstructionWindow.get 166, by decide⟩,
   ⟨3942, .op .SHR, by exact GuardInstructionWindow.get 167, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3943, .op .XOR, by exact GuardInstructionWindow.get 168, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3944, .push ⟨2, by decide⟩ (UInt256.ofNat 335), by exact GuardInstructionWindow.get 169, by decide⟩,
   ⟨3945, .op .JUMPI, by exact GuardInstructionWindow.get 170, ⟨by decide, trivial, rfl⟩⟩]

def storePath : List Located :=
  [⟨3946, .push ⟨20, by decide⟩ (UInt256.ofNat 890993315260586290631548281360202943075753233713), by exact GuardInstructionWindow.get 171, by decide⟩,
   ⟨3947, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 172, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3948, .push ⟨2, by decide⟩ (UInt256.ofNat 417), by exact GuardInstructionWindow.get 173, by decide⟩,
   ⟨3949, .op .JUMP, by exact GuardInstructionWindow.get 174, ⟨by decide, trivial, rfl⟩⟩,
   ⟨275, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨276, .push ⟨21, by decide⟩ (UInt256.ofNat 25448770637332498804579667936807160623886401639), by rfl, by decide⟩,
   ⟨277, .op .MUL, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨278, .op (.Swap ⟨0, by decide⟩), by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨279, .op .SUB, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨280, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨281, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨283, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨284, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def sizeCond (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2)
def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (leadWord input)
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621))
def armEntry (input : ByteArray) : State := Execution.atPC input 5151
def fallbackState (input : ByteArray) : State := Execution.atPC input 335
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
    pc := UInt256.ofNat 445
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def sized (input : ByteArray) : State :=
  {stored input with pc := UInt256.ofNat 446, stack := [UInt256.ofNat 32]}
def returned (input : ByteArray) : State :=
  {stored input with
    pc := UInt256.ofNat 447
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

theorem arm_dest : Decode.isValidJumpDest submissionBytecode 5151 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3930 (by exact GuardInstructionWindow.get 155)
  rw [pc_4089] at h
  exact h
private theorem valid_generic : Decode.isValidJumpDest submissionBytecode 335 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 230 (by rfl)
  rw [pc_176] at h
  exact h
private theorem valid_return : Decode.isValidJumpDest submissionBytecode 417 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 275 (by rfl)
  rw [pc_236] at h
  exact h

theorem run_large (input : ByteArray) (hm : sizeCond input ≠ 0) :
    Stepper.runLocatedBlock sizePath (armEntry input) = some (fallbackState input) := by
  have ht := true_of_ne_zero (sizeCond input) hm
  simp [sizeCond] at ht
  simp [sizePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    armEntry, fallbackState, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, ht, valid_generic]

theorem run_small (input : ByteArray) (hm : sizeCond input = 0) :
    Stepper.runLocatedBlock sizePath (armEntry input) =
      some (Execution.atPC input 5160) := by
  have ht : ¬ UInt256.isTrue (sizeCond input) := by rw [hm]; decide
  simp [sizeCond] at ht
  simp [sizePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    armEntry, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, ht]

theorem run_word_miss (input : ByteArray) (hm : wordCond input ≠ 0) :
    Stepper.runLocatedBlock wordPath (Execution.atPC input 5160) =
      some (fallbackState input) := by
  have ht := true_of_ne_zero (wordCond input) hm
  simp [wordCond, leadWord] at ht
  simp [wordPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    fallbackState, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht, valid_generic]

theorem run_word_hit (input : ByteArray) (hm : wordCond input = 0) :
    Stepper.runLocatedBlock wordPath (Execution.atPC input 5160) =
      some (Execution.atPC input 5176) := by
  have ht : ¬ UInt256.isTrue (wordCond input) := by rw [hm]; decide
  simp [wordCond, leadWord] at ht
  simp [wordPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, ht]

theorem run_store (input : ByteArray) :
    Stepper.runLocatedBlock storePath (Execution.atPC input 5176) = some (stored input) := by
  simp [storePath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Execution.atPC, initialState, stored, answerMemory, answerBytes, answerWord,
    EmptySpec.digestNat, UInt256.succ, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, Word.word_toNat_ofNat, Word.ofNat_add_mod,
    mul_op, sub_op, valid_return, List.exchange, List.getElem?_cons_zero]

theorem run_finish (input : ByteArray) :
    Stepper.runLocatedBlock finishPath (sized input) = some (returned input) := by
  simp [finishPath, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    sized, stored, returned, UInt256.succ, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, Word.word_toNat_ofNat, Word.ofNat_add_mod,
    mul_op, sub_op, initialState]

private def sound (path : List Located) {s t : State}
    (h : Stepper.runLocatedBlock path s = some t)
    (hc : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hf : s.fork = .Osaka := by rfl) (hr : s.halt = .Running := by rfl)
    (hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by exact deployAddress_not_precompile) :
    GasSteps s t :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path hc hf h hr hn

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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 282 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (stored input).pc.toNat = Artifact.submissionArtifact.instructionPC 282 := by
    rw [pc_243]; rfl
  have hop : (stored input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (stored input) 282 rfl hp .MSIZE none hd rfl
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
