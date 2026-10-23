import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcSizeGuard
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.GuardInstructionWindow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuardLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcRecognition
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.AbcArm
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open TinyGuardLogic
abbrev Located := DataStepper.Located HoistedInherited.Artifact.submissionArtifact .Osaka

@[simp] theorem pc_4095 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3405 = 4665 := by
  exact HoistedInherited.GuardInstructionWindow.pc 0
@[simp] theorem pc_4096 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3406 = 4698 := by
  exact HoistedInherited.GuardInstructionWindow.pc 1
@[simp] theorem pc_4097 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3407 = 4699 := by
  exact HoistedInherited.GuardInstructionWindow.pc 2
@[simp] theorem pc_4098 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3408 = 4700 := by
  exact HoistedInherited.GuardInstructionWindow.pc 3
@[simp] theorem pc_4101 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3409 = 4701 := by
  exact HoistedInherited.GuardInstructionWindow.pc 4
@[simp] theorem pc_4102 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3410 = 4702 := by
  exact HoistedInherited.GuardInstructionWindow.pc 5
@[simp] theorem pc_4103 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3411 = 4703 := by
  exact HoistedInherited.GuardInstructionWindow.pc 6
@[simp] theorem pc_4104 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3412 = 4706 := by
  exact HoistedInherited.GuardInstructionWindow.pc 7
@[simp] theorem pc_4105 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3413 = 4707 := by
  exact HoistedInherited.GuardInstructionWindow.pc 8
@[simp] theorem pc_241 : HoistedInherited.Artifact.submissionArtifact.instructionPC 3414 = 4728 := by
  exact HoistedInherited.GuardInstructionWindow.pc 9
@[simp] theorem pc_inlineStore : HoistedInherited.Artifact.submissionArtifact.instructionPC 3415 = 4729 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineMsize : HoistedInherited.Artifact.submissionArtifact.instructionPC 3416 = 4730 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineZero : HoistedInherited.Artifact.submissionArtifact.instructionPC 3417 = 4731 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_inlineReturn : HoistedInherited.Artifact.submissionArtifact.instructionPC 3418 = 4732 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyDest : HoistedInherited.Artifact.submissionArtifact.instructionPC 4361 = 7019 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyPush : HoistedInherited.Artifact.submissionArtifact.instructionPC 4362 = 7020 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyZero0 : HoistedInherited.Artifact.submissionArtifact.instructionPC 4363 = 7041 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyStore : HoistedInherited.Artifact.submissionArtifact.instructionPC 4364 = 7042 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyMsize : HoistedInherited.Artifact.submissionArtifact.instructionPC 4365 = 7043 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyZero1 : HoistedInherited.Artifact.submissionArtifact.instructionPC 4366 = 7044 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_emptyReturn : HoistedInherited.Artifact.submissionArtifact.instructionPC 4367 = 7045 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def wordMaskNat : Nat :=
  5506022574726681700290820341793915503137370776112178186780075461015395893248

def wordMask : UInt256 := UInt256.ofNat wordMaskNat

def wordPath : List Located :=
    [⟨3405, .push ⟨32, by decide⟩ wordMask, by exact HoistedInherited.GuardInstructionWindow.get 0, by decide⟩,
     ⟨3406, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact HoistedInherited.GuardInstructionWindow.get 1, by decide⟩,
     ⟨3407, .op .CALLDATALOAD, by exact HoistedInherited.GuardInstructionWindow.get 2, ⟨by decide, trivial, rfl⟩⟩,
     ⟨3408, .op .CALLDATASIZE, by exact HoistedInherited.GuardInstructionWindow.get 3, ⟨by decide, trivial, rfl⟩⟩,
     ⟨3409, .op .SAR, by exact HoistedInherited.GuardInstructionWindow.get 4, ⟨by decide, trivial, rfl⟩⟩,
     ⟨3410, .op .XOR, by exact HoistedInherited.GuardInstructionWindow.get 5, ⟨by decide, trivial, rfl⟩⟩,
     ⟨3411, .push ⟨2, by decide⟩ (UInt256.ofNat 245), by exact HoistedInherited.GuardInstructionWindow.get 6, by decide⟩,
     ⟨3412, .op .JUMPI, by exact HoistedInherited.GuardInstructionWindow.get 7, ⟨by decide, trivial, rfl⟩⟩]

def storePath : List Located :=
  [⟨3413, .push ⟨20, by decide⟩ (UInt256.ofNat 814647003348588794217809277549781461204094028796), by exact HoistedInherited.GuardInstructionWindow.get 8, by decide⟩,
   ⟨3414, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3415, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨3417, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨3418, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def emptyStorePath : List Located :=
  [⟨4361, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨4362, .push ⟨20, by decide⟩ (UInt256.ofNat 890993315260586290631548281360202943075753233713), by rfl, by decide⟩,
   ⟨4363, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4364, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def emptyFinishPath : List Located :=
  [⟨4366, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨4367, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def maskedWord (input : ByteArray) : UInt256 :=
  MachineState.readWord input 0

def shiftedWord (input : ByteArray) : UInt256 :=
  UInt256.sar (maskedWord input) (UInt256.ofNat input.size)

def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (shiftedWord input) wordMask

def armEntry (input : ByteArray) : State := HoistedInherited.Execution.atPC input 4665
def emptyEntry (input : ByteArray) : State := HoistedInherited.Execution.atPC input 7019
def fallbackState (input : ByteArray) : State := HoistedInherited.Execution.atPC input 245
def answerWord (input : ByteArray) : UInt256 :=
  if input.size = 0 then UInt256.ofNat 890993315260586290631548281360202943075753233713
  else UInt256.ofNat 814647003348588794217809277549781461204094028796
def answerBytes (input : ByteArray) : ByteArray :=
  Data.Bytes.natToBytesPadded (answerWord input).toNat 32
def answerMemory (input : ByteArray) : ByteArray :=
  MachineState.writeBytes ByteArray.empty (answerBytes input) 0
def stored (input : ByteArray) : State :=
  {initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4730
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def sized (input : ByteArray) : State :=
  {stored input with pc := UInt256.ofNat 4731, stack := [UInt256.ofNat 32]}
def returned (input : ByteArray) : State :=
  {stored input with
    pc := UInt256.ofNat 4732
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory input) 0 32}
def emptyStored (input : ByteArray) : State :=
  {initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 7043
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def emptySized (input : ByteArray) : State :=
  {emptyStored input with pc := UInt256.ofNat 7044, stack := [UInt256.ofNat 32]}
def emptyReturned (input : ByteArray) : State :=
  {emptyStored input with
    pc := UInt256.ofNat 7045
    halt := .Returned
    hReturn := MachineState.readPadded (answerMemory input) 0 32}

@[simp] private theorem add_nat (a b : Nat) :
    UInt256.add (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a + b) :=
  Word.ofNat_add_mod a b
@[simp] private theorem zero_toNat : ({val := 0} : UInt256).toNat = 0 := rfl
@[simp] private theorem literal_zero_toNat : (0 : UInt256).toNat = 0 := rfl

private theorem true_of_ne_zero (w : UInt256) (h : w ≠ 0) : UInt256.isTrue w = true := by
  have ht : UInt256.isTrue w := by
    intro hn
    apply h
    apply Word.word_ext
    exact hn
  simpa using ht

private theorem valid_generic : Decode.isValidJumpDest submissionBytecode 245 = true := by
  have hp : HoistedInherited.Artifact.submissionArtifact.instructionPC 125 = 245 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := HoistedInherited.Artifact.submissionArtifact.isValidJumpDest_index 125 (by rfl)
  rw [hp] at h
  exact h

/-! ### The size-fed sign-extending guard accepts exactly `abc`. -/
private theorem shiftedWord_eq_of_wordCond (input : ByteArray) (hz : wordCond input = 0) :
    (shiftedWord input).toNat = AbcSizeGuard.target := by
  have h := congrArg UInt256.toNat ((KnownInputLogic.wordXor_eq_zero_iff _ _).mp hz)
  exact h

theorem size_lt_four_of_wordCond (input : ByteArray) (hfit : CalldataFits input)
    (hz : wordCond input = 0) : input.size < 4 := by
  have h := AbcSizeGuard.shift_hit_small _ _ (shiftedWord_eq_of_wordCond input hz)
  have hs : (UInt256.ofNat input.size).toNat = input.size := by
    rw [Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hfit (by norm_num))
  rw [hs] at h
  exact h

theorem wordCond_zero_size_pos (input : ByteArray) (hfit : CalldataFits input)
    (_hpos : 0 < input.size) (_hsmall : input.size < 4) (hz : wordCond input = 0) :
    input = AbcInputData.abcInput :=
  AbcSizeGuard.guard_sound input hfit (shiftedWord_eq_of_wordCond input hz)

private def sarStep {s : State} {shift value : UInt256} {rest : List UInt256}
    (hop : s.decodedOp = some .SAR)
    (hstack : s.stack = shift :: value :: rest)
    (hcap : s.stack.length + Operation.pushArity .SAR ≤ 1024 + Operation.popArity .SAR)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps s { s with stack := UInt256.sar value shift :: rest, pc := s.pc.succ } := by
  let cost := Gas.baseCost s.fork .SAR
  apply GasStep.of_running cost hrun hnp
  intro gas hgas
  simpa [withGas, cost] using
    StepRunning.sar (withGas s gas) shift value rest hop hgas hstack hcap

/-! ### The word test, with the sign-extending shift stepped directly -/

def wordHead : List Located := wordPath.take 4
def wordCalc : List Located := (wordPath.drop 5).take 2
def wordBranch : Located :=
  ⟨3412, .op .JUMPI, by exact HoistedInherited.GuardInstructionWindow.get 7, ⟨by decide, trivial, rfl⟩⟩
def wordLoaded (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4701
    stack := [UInt256.ofNat input.size, maskedWord input, wordMask] }
def wordShifted (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4702
    stack := [shiftedWord input, wordMask] }
def wordTested (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4706
    stack := [UInt256.ofNat 245, wordCond input] }

private theorem run_word_head (input : ByteArray) :
    DataStepper.runLocatedBlock wordHead (armEntry input) = some (wordLoaded input) := by
  simp [wordHead, wordPath, HoistedInherited.Artifact.op, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    armEntry, wordLoaded, maskedWord, wordMask, HoistedInherited.Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, List.getElem?_cons_zero]
private theorem run_word_calc (input : ByteArray) :
    DataStepper.runLocatedBlock wordCalc (wordShifted input) = some (wordTested input) := by
  simp [wordCalc, wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    wordShifted, wordTested, wordCond, HoistedInherited.Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat]

private def gasSteps_sar (input : ByteArray) : GasSteps (wordLoaded input) (wordShifted input) := by
  have hd := HoistedInherited.Artifact.submissionArtifact.decodeAt_op_index 3409 .SAR
    (by exact HoistedInherited.GuardInstructionWindow.get 4) (by decide) trivial
  have hp : (wordLoaded input).pc.toNat = HoistedInherited.Artifact.submissionArtifact.instructionPC 3409 := by
    rw [pc_4101]; rfl
  have hop : (wordLoaded input).decodedOp = some .SAR :=
    HoistedInherited.Artifact.submissionArtifact.state_decodedOp_of (wordLoaded input) 3409 rfl hp .SAR none hd rfl
  have g := sarStep (s := wordLoaded input) (shift := UInt256.ofNat input.size)
    (value := maskedWord input) (rest := [wordMask]) hop rfl
    (by show 3 + Operation.pushArity .SAR ≤ 1024 + Operation.popArity .SAR; decide) rfl
    deployAddress_not_precompile
  have ht : { wordLoaded input with
      stack := UInt256.sar (maskedWord input) (UInt256.ofNat input.size) :: [wordMask],
      pc := (wordLoaded input).pc.succ } = wordShifted input := by
    simp [wordLoaded, wordShifted, shiftedWord, initialState, Word.succ_ofNat_mod,
      Word.word_toNat_ofNat]
  exact GasSteps.cast g rfl ht

private def soundW (path : List Located) {s t : State}
    (h : DataStepper.runLocatedBlock path s = some t)
    (hc : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code := by rfl)
    (hf : s.fork = .Osaka := by rfl) (hr : s.halt = .Running := by rfl)
    (hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by exact deployAddress_not_precompile) :
    GasSteps s t :=
  DataStepper.runLocatedBlock_sound HoistedInherited.Artifact.submissionArtifact .Osaka path hc hf h hr hn

private def gasSteps_word_prefix (input : ByteArray) :
    GasSteps (armEntry input) (wordTested input) :=
  (soundW wordHead (run_word_head input)).trans
    ((gasSteps_sar input).trans (soundW wordCalc (run_word_calc input)))

theorem run_word_miss (input : ByteArray) (hm : wordCond input ≠ 0) :
    DataStepper.runLocatedBlock [wordBranch] (wordTested input) =
      some (fallbackState input) := by
  exact PatternedScan.blockOfS wordBranch
    (PatternedScan.pcFactS input 3412 4706 [UInt256.ofNat 245, wordCond input] (by norm_num) pc_4104)
    (PatternedScan.stepS_jumpi_taken input 4706 245 (UInt256.ofNat 245) (wordCond input) []
      (by simp) (by norm_num) rfl (by simpa using true_of_ne_zero (wordCond input) hm) valid_generic)

theorem run_word_hit (input : ByteArray) (hm : wordCond input = 0) :
    DataStepper.runLocatedBlock [wordBranch] (wordTested input) = some (HoistedInherited.Execution.atPC input 4707) := by
  have ht : ¬ UInt256.isTrue (wordCond input) := by rw [hm]; decide
  exact PatternedScan.blockOfS wordBranch
    (PatternedScan.pcFactS input 3412 4706 [UInt256.ofNat 245, wordCond input] (by norm_num) pc_4104)
    (PatternedScan.stepS_jumpi_fall input 4706 (UInt256.ofNat 245) (wordCond input) []
      (by simp) (by norm_num) ht)

theorem run_store (input : ByteArray) (hne : input.size ≠ 0) :
    DataStepper.runLocatedBlock storePath (HoistedInherited.Execution.atPC input 4707) = some (stored input) := by
  simp (config := { maxSteps := 1000000 })
    [storePath, DataStepper.runLocatedBlock, DataStepper.runLocated,
     DataStepper.runInstr, PatternedScan.stS, HoistedInherited.Execution.atPC, stored, answerMemory, answerBytes,
     answerWord, hne, MachineState.mstore, State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
     initialState, Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     Word.word_toNat_ofNat, UInt256.succ, List.exchange, List.getElem?_cons_zero]

theorem run_finish (input : ByteArray) :
    DataStepper.runLocatedBlock finishPath (sized input) = some (returned input) := by
  simp (config := { maxSteps := 1000000 })
    [finishPath, DataStepper.runLocatedBlock, DataStepper.runLocated,
     DataStepper.runInstr, sized, stored, returned, initialState,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
     Word.word_toNat_ofNat, UInt256.succ, List.exchange, List.getElem?_cons_zero]

theorem run_empty_store (input : ByteArray) (hz : input.size = 0) :
    DataStepper.runLocatedBlock emptyStorePath (emptyEntry input) = some (emptyStored input) := by
  simp (config := { maxSteps := 1000000 })
    [emptyStorePath, DataStepper.runLocatedBlock, DataStepper.runLocated,
     DataStepper.runInstr, PatternedScan.stS, emptyEntry, HoistedInherited.Execution.atPC, emptyStored, answerMemory, answerBytes,
     answerWord, hz, MachineState.mstore, State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
     initialState, Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     Word.word_toNat_ofNat, UInt256.succ, List.exchange, List.getElem?_cons_zero]

theorem run_empty_finish (input : ByteArray) :
    DataStepper.runLocatedBlock emptyFinishPath (emptySized input) = some (emptyReturned input) := by
  simp (config := { maxSteps := 1000000 })
    [emptyFinishPath, DataStepper.runLocatedBlock, DataStepper.runLocated,
     DataStepper.runInstr, emptySized, emptyStored, emptyReturned, initialState,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
     Word.word_toNat_ofNat, UInt256.succ, List.exchange, List.getElem?_cons_zero]

private def sound (path : List Located) {s t : State}
    (h : DataStepper.runLocatedBlock path s = some t)
    (hc : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code := by rfl)
    (hf : s.fork = .Osaka := by rfl) (hr : s.halt = .Running := by rfl)
    (hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by exact deployAddress_not_precompile) :
    GasSteps s t :=
  DataStepper.runLocatedBlock_sound HoistedInherited.Artifact.submissionArtifact .Osaka path hc hf h hr hn

def gasSteps_miss (input : ByteArray) (hw : wordCond input ≠ 0) :
    GasSteps (armEntry input) (fallbackState input) :=
  (gasSteps_word_prefix input).trans (sound [wordBranch] (run_word_miss input hw))

def gasSteps_hit (input : ByteArray) (hw : wordCond input = 0) (hne : input.size ≠ 0) :
    GasSteps (armEntry input) (returned input) := by
  have gw := (gasSteps_word_prefix input).trans (sound [wordBranch] (run_word_hit input hw))
  have gs := sound storePath (run_store input hne)
  have hd := HoistedInherited.Artifact.submissionArtifact.decodeAt_op_index 3416 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (stored input).pc.toNat = HoistedInherited.Artifact.submissionArtifact.instructionPC 3416 := by
    rw [pc_inlineMsize]; rfl
  have hop : (stored input).decodedOp = some .MSIZE :=
    HoistedInherited.Artifact.submissionArtifact.state_decodedOp_of (stored input) 3416 rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  have gm : GasSteps (stored input) (sized input) := by
    simpa [stored, sized, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := sound finishPath (run_finish input)
  exact gw.trans (gs.trans (gm.trans gf))

def gasSteps_empty_hit (input : ByteArray) (hz : input.size = 0) :
    GasSteps (emptyEntry input) (emptyReturned input) := by
  have gs := sound emptyStorePath (run_empty_store input hz)
  have hd := HoistedInherited.Artifact.submissionArtifact.decodeAt_op_index 4365 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (emptyStored input).pc.toNat = HoistedInherited.Artifact.submissionArtifact.instructionPC 4365 := by
    rw [pc_emptyMsize]; rfl
  have hop : (emptyStored input).decodedOp = some .MSIZE :=
    HoistedInherited.Artifact.submissionArtifact.state_decodedOp_of (emptyStored input) 4365 rfl hp .MSIZE none hd rfl
  have gmraw := Msize.step hop (by change (0 : Nat) < 1024; decide)
    rfl deployAddress_not_precompile
  have gm : GasSteps (emptyStored input) (emptySized input) := by
    simpa [emptyStored, emptySized, initialState, Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := sound emptyFinishPath (run_empty_finish input)
  exact gs.trans (gm.trans gf)

theorem answer_empty : answerBytes ByteArray.empty = EmptySpec.emptyOutput := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide
theorem answer_abc : answerBytes AbcInputData.abcInput = AbcInputData.abcPaddedDigest := by
  rw [answerBytes, Memory.natToBytesPadded_eq_natToBE]
  decide

private theorem readWord_empty : MachineState.readWord ByteArray.empty 0 = 0 := by
  unfold MachineState.readWord
  rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

private theorem readWord_abc :
    MachineState.readWord AbcInputData.abcInput 0 = UInt256.ofNat (0x616263 * 2 ^ 232) := by
  unfold MachineState.readWord
  rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList,
    YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem wordCond_empty : wordCond ByteArray.empty ≠ 0 := by
  unfold wordCond shiftedWord maskedWord
  rw [readWord_empty]
  decide

theorem wordCond_abc : wordCond AbcInputData.abcInput = 0 := by
  unfold wordCond shiftedWord maskedWord
  rw [readWord_abc]
  decide

private theorem correct_known (input : ByteArray)
    (hw : wordCond input = 0) (hne : input.size ≠ 0) (hspec : spec input = answerBytes input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := entryPrefix.trans (gasSteps_hit input hw hne)
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

theorem correct_abc (input : ByteArray) (_hfit : CalldataFits input)
    (heq : input = AbcInputData.abcInput)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  subst input
  exact correct_known _ wordCond_abc (by decide) (by rw [AbcDigest.spec_abc, answer_abc]) entryPrefix

theorem correct_empty (input : ByteArray) (_hfit : CalldataFits input)
    (heq : input = ByteArray.empty)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (emptyEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  subst input
  let trace := entryPrefix.trans (gasSteps_empty_hit ByteArray.empty rfl)
  have hsize : (answerBytes ByteArray.empty).size = 32 :=
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size _ _
  have hread : MachineState.readPadded (answerMemory ByteArray.empty) 0 32 = answerBytes ByteArray.empty := by
    rw [← hsize]
    exact Memory.readPadded_writeBytes_same ByteArray.empty (answerBytes ByteArray.empty) 0
  have hspec : spec ByteArray.empty = answerBytes ByteArray.empty := by
    rw [EmptySpec.spec_empty, answer_empty]
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, emptyReturned, emptyStored, State.isDone, State.isHalted, State.isRunning]
    rfl)
  rw [State.toResult_returned _ (by rfl)] at heval
  change Eval (withGas (initialState submissionBytecode ByteArray.empty 0) gas)
    (.returned (MachineState.readPadded (answerMemory ByteArray.empty) 0 32)) at heval
  rw [hread, ← hspec] at heval
  exact heval

#print axioms correct_abc
#print axioms correct_empty
#print axioms gasSteps_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.AbcArm
