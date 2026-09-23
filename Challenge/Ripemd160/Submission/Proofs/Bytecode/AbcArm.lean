import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
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

@[simp] theorem pc_176 : Artifact.submissionArtifact.instructionPC 222 = 339 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4095 : Artifact.submissionArtifact.instructionPC 3647 = 4854 := by
  exact GuardInstructionWindow.pc 0
@[simp] theorem pc_4096 : Artifact.submissionArtifact.instructionPC 3648 = 4855 := by
  exact GuardInstructionWindow.pc 1
@[simp] theorem pc_4097 : Artifact.submissionArtifact.instructionPC 3649 = 4856 := by
  exact GuardInstructionWindow.pc 2
@[simp] theorem pc_4098 : Artifact.submissionArtifact.instructionPC 3650 = 4858 := by
  exact GuardInstructionWindow.pc 3
@[simp] theorem pc_4099 : Artifact.submissionArtifact.instructionPC 3651 = 4859 := by
  exact GuardInstructionWindow.pc 4
@[simp] theorem pc_4100 : Artifact.submissionArtifact.instructionPC 3652 = 4860 := by
  exact GuardInstructionWindow.pc 5
@[simp] theorem pc_4101 : Artifact.submissionArtifact.instructionPC 3653 = 4864 := by
  exact GuardInstructionWindow.pc 6
@[simp] theorem pc_4102 : Artifact.submissionArtifact.instructionPC 3654 = 4865 := by
  exact GuardInstructionWindow.pc 7
@[simp] theorem pc_4103 : Artifact.submissionArtifact.instructionPC 3655 = 4866 := by
  exact GuardInstructionWindow.pc 8
@[simp] theorem pc_4104 : Artifact.submissionArtifact.instructionPC 3656 = 4869 := by
  exact GuardInstructionWindow.pc 9
@[simp] theorem pc_4105 : Artifact.submissionArtifact.instructionPC 3657 = 4870 := by
  exact GuardInstructionWindow.pc 10
@[simp] theorem pc_4106 : Artifact.submissionArtifact.instructionPC 3658 = 4891 := by
  exact GuardInstructionWindow.pc 11
@[simp] theorem pc_4107 : Artifact.submissionArtifact.instructionPC 3659 = 4892 := by
  exact GuardInstructionWindow.pc 12
@[simp] theorem pc_4108 : Artifact.submissionArtifact.instructionPC 3660 = 4893 := by
  exact GuardInstructionWindow.pc 13
@[simp] theorem pc_4109 : Artifact.submissionArtifact.instructionPC 3661 = 4914 := by
  exact GuardInstructionWindow.pc 14
@[simp] theorem pc_241 : Artifact.submissionArtifact.instructionPC 3662 = 4915 := by
  exact GuardInstructionWindow.pc 15
@[simp] theorem pc_242 : Artifact.submissionArtifact.instructionPC 3663 = 4916 := by
  exact GuardInstructionWindow.pc 16
@[simp] theorem pc_243 : Artifact.submissionArtifact.instructionPC 3664 = 4917 := by
  exact GuardInstructionWindow.pc 17
@[simp] theorem pc_244 : Artifact.submissionArtifact.instructionPC 3665 = 4918 := by
  exact GuardInstructionWindow.pc 18
@[simp] theorem pc_245 : Artifact.submissionArtifact.instructionPC 3666 = 4919 := by
  exact GuardInstructionWindow.pc 19

def entryDest : Located :=
  ⟨222, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩

def wordPath : List Located :=
  [⟨3647, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 0, by decide⟩,
   ⟨3648, .op .CALLDATALOAD, by exact GuardInstructionWindow.get 1, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3649, .push ⟨1, by decide⟩ (UInt256.ofNat 232), by exact GuardInstructionWindow.get 2, by decide⟩,
   ⟨3650, .op .SHR, by exact GuardInstructionWindow.get 3, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3651, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 4, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3652, .push ⟨3, by decide⟩ (UInt256.ofNat 2127393), by exact GuardInstructionWindow.get 5, by decide⟩,
   ⟨3653, .op .MUL, by exact GuardInstructionWindow.get 6, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3654, .op .XOR, by exact GuardInstructionWindow.get 7, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3655, .push ⟨2, by decide⟩ (UInt256.ofNat 339), by exact GuardInstructionWindow.get 8, by decide⟩,
   ⟨3656, .op .JUMPI, by exact GuardInstructionWindow.get 9, ⟨by decide, trivial, rfl⟩⟩]

def wordMissPath : List Located := wordPath ++ [entryDest]

def storePath : List Located :=
  [⟨3657, .push ⟨20, by decide⟩ (UInt256.ofNat 95383801997447390147238369573240532004699299169), by exact GuardInstructionWindow.get 10, by decide⟩,
   ⟨3658, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 11, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3659, .op .SHR, by exact GuardInstructionWindow.get 12, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3660, .push ⟨20, by decide⟩ (UInt256.ofNat 802931186561056611446976448233794645126013734992), by exact GuardInstructionWindow.get 13, by decide⟩,
   ⟨3661, .op .XOR, by exact GuardInstructionWindow.get 14, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3662, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 15, by decide⟩,
   ⟨3663, .op .MSTORE, by exact GuardInstructionWindow.get 16, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨3665, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 18, by decide⟩,
   ⟨3666, .op .RETURN, by exact GuardInstructionWindow.get 19, ⟨by decide, trivial, rfl⟩⟩]

def sizeCond (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2)
def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (leadWord input)
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621))
def armEntry (input : ByteArray) : State := Execution.atPC input 4854
def fallbackState (input : ByteArray) : State := Execution.atPC input 340
def answerWord (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 802931186561056611446976448233794645126013734992)
    (UInt256.shiftRight (UInt256.ofNat 95383801997447390147238369573240532004699299169)
      (UInt256.ofNat input.size))
def answerBytes (input : ByteArray) : ByteArray :=
  Data.Bytes.natToBytesPadded (answerWord input).toNat 32
def answerMemory (input : ByteArray) : ByteArray :=
  MachineState.writeBytes ByteArray.empty (answerBytes input) 0
def stored (input : ByteArray) : State :=
  {initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4917
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def sized (input : ByteArray) : State :=
  {stored input with pc := UInt256.ofNat 4918, stack := [UInt256.ofNat 32]}
def returned (input : ByteArray) : State :=
  {stored input with
    pc := UInt256.ofNat 4919
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

private theorem valid_generic : Decode.isValidJumpDest submissionBytecode 339 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 222 (by rfl)
  rw [pc_176] at h
  exact h
def wordHead : List Located := wordPath.take 5
def wordCalc : List Located := (wordPath.drop 5).take 4
def wordBranch : Located :=
  ⟨3656, .op .JUMPI, by exact GuardInstructionWindow.get 9, ⟨by decide, trivial, rfl⟩⟩
def wordMiddle (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4860
    stack := [UInt256.ofNat input.size, leadWord input] }
def wordTested (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4869
    stack := [UInt256.ofNat 339, wordCond input] }

private theorem run_word_head (input : ByteArray) :
    DataStepper.runLocatedBlock wordHead (armEntry input) = some (wordMiddle input) := by
  simp [wordHead, wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    armEntry, wordMiddle, Execution.atPC, initialState, UInt256.succ, leadWord,
    Word.ofNat_add_mod, Word.word_toNat_ofNat]
private theorem run_word_calc (input : ByteArray) :
    DataStepper.runLocatedBlock wordCalc (wordMiddle input) = some (wordTested input) := by
  simp [wordCalc, wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    wordMiddle, wordTested, wordCond, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, RawExpressionAC.mul_comm, RawExpressionAC.xor_comm]
private theorem run_word_prefix (input : ByteArray) :
    DataStepper.runLocatedBlock (wordPath.take 9) (armEntry input) = some (wordTested input) := by
  exact DataStepper.runLocatedBlock_append wordHead wordCalc _ _ _ (run_word_head input) rfl (run_word_calc input)

theorem run_word_miss (input : ByteArray) (hm : wordCond input ≠ 0) :
    DataStepper.runLocatedBlock wordMissPath (armEntry input) = some (fallbackState input) := by
  have hbranch : DataStepper.runLocatedBlock [wordBranch] (wordTested input) =
      some (PatternedScan.stS input 339 []) :=
    PatternedScan.blockOfS wordBranch
      (PatternedScan.pcFactS input 3656 4869 [UInt256.ofNat 339, wordCond input] (by norm_num) pc_4104)
      (PatternedScan.stepS_jumpi_taken input 4869 339 (UInt256.ofNat 339) (wordCond input) []
        (by simp) (by norm_num) rfl (by simpa using true_of_ne_zero (wordCond input) hm) valid_generic)
  have hd : DataStepper.runLocatedBlock [entryDest] (PatternedScan.stS input 339 []) =
      some (fallbackState input) := by
    exact PatternedScan.blockOfS entryDest
      (PatternedScan.pcFactS input 222 339 [] (by norm_num) pc_176)
      (PatternedScan.stepS_jumpdest input 339 [] (by simp) (by norm_num))
  have hbe := DataStepper.runLocatedBlock_append [wordBranch] [entryDest]
    _ _ _ hbranch rfl hd
  exact DataStepper.runLocatedBlock_append (wordPath.take 9) [wordBranch, entryDest]
    _ _ _ (run_word_prefix input) rfl hbe

theorem run_word_hit (input : ByteArray) (hm : wordCond input = 0) :
    DataStepper.runLocatedBlock wordPath (armEntry input) = some (Execution.atPC input 4870) := by
  have ht : ¬ UInt256.isTrue (wordCond input) := by rw [hm]; decide
  have hbranch : DataStepper.runLocatedBlock [wordBranch] (wordTested input) = some (Execution.atPC input 4870) :=
    PatternedScan.blockOfS wordBranch
      (PatternedScan.pcFactS input 3656 4869 [UInt256.ofNat 339, wordCond input] (by norm_num) pc_4104)
      (PatternedScan.stepS_jumpi_fall input 4869 (UInt256.ofNat 339) (wordCond input) []
        (by simp) (by norm_num) ht)
  exact DataStepper.runLocatedBlock_append (wordPath.take 9) [wordBranch] _ _ _ (run_word_prefix input) rfl hbranch

theorem run_store (input : ByteArray) :
    DataStepper.runLocatedBlock storePath (Execution.atPC input 4870) = some (stored input) := by
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
  sound wordMissPath (run_word_miss input hw)

def gasSteps_hit (input : ByteArray) (hw : wordCond input = 0) :
    GasSteps (armEntry input) (returned input) := by
  have gw := sound wordPath (run_word_hit input hw)
  have gs := sound storePath (run_store input)
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3664 .MSIZE
    (by exact GuardInstructionWindow.get 17) (by decide) trivial
  have hp : (stored input).pc.toNat = Artifact.submissionArtifact.instructionPC 3664 := by
    rw [pc_243]; rfl
  have hop : (stored input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (stored input) 3664 rfl hp .MSIZE none hd rfl
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
