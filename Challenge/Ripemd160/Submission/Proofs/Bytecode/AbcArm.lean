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

@[simp] theorem pc_176 : Artifact.submissionArtifact.instructionPC 148 = 246 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_4095 : Artifact.submissionArtifact.instructionPC 3530 = 4740 := by
  exact GuardInstructionWindow.pc 0
@[simp] theorem pc_4096 : Artifact.submissionArtifact.instructionPC 3531 = 4741 := by
  exact GuardInstructionWindow.pc 1
@[simp] theorem pc_4097 : Artifact.submissionArtifact.instructionPC 3532 = 4742 := by
  exact GuardInstructionWindow.pc 2
@[simp] theorem pc_4098 : Artifact.submissionArtifact.instructionPC 3533 = 4744 := by
  exact GuardInstructionWindow.pc 3
@[simp] theorem pc_4099 : Artifact.submissionArtifact.instructionPC 3534 = 4745 := by
  exact GuardInstructionWindow.pc 4
@[simp] theorem pc_4100 : Artifact.submissionArtifact.instructionPC 3535 = 4746 := by
  exact GuardInstructionWindow.pc 5
@[simp] theorem pc_4101 : Artifact.submissionArtifact.instructionPC 3536 = 4750 := by
  exact GuardInstructionWindow.pc 6
@[simp] theorem pc_4102 : Artifact.submissionArtifact.instructionPC 3537 = 4751 := by
  exact GuardInstructionWindow.pc 7
@[simp] theorem pc_4103 : Artifact.submissionArtifact.instructionPC 3538 = 4752 := by
  exact GuardInstructionWindow.pc 8
@[simp] theorem pc_4104 : Artifact.submissionArtifact.instructionPC 3539 = 4754 := by
  exact GuardInstructionWindow.pc 9
@[simp] theorem pc_4105 : Artifact.submissionArtifact.instructionPC 3540 = 4755 := by
  exact GuardInstructionWindow.pc 10
@[simp] theorem pc_4106 : Artifact.submissionArtifact.instructionPC 3541 = 4776 := by
  exact GuardInstructionWindow.pc 11
@[simp] theorem pc_4107 : Artifact.submissionArtifact.instructionPC 3542 = 4777 := by
  exact GuardInstructionWindow.pc 12
@[simp] theorem pc_4108 : Artifact.submissionArtifact.instructionPC 3543 = 4778 := by
  exact GuardInstructionWindow.pc 13
@[simp] theorem pc_4109 : Artifact.submissionArtifact.instructionPC 3544 = 4799 := by
  exact GuardInstructionWindow.pc 14
@[simp] theorem pc_241 : Artifact.submissionArtifact.instructionPC 3545 = 4800 := by
  exact GuardInstructionWindow.pc 15
@[simp] theorem pc_242 : Artifact.submissionArtifact.instructionPC 3546 = 4802 := by
  exact GuardInstructionWindow.pc 16
@[simp] theorem pc_ret55 : Artifact.submissionArtifact.instructionPC 55 = 98 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_ret56 : Artifact.submissionArtifact.instructionPC 56 = 99 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_ret57 : Artifact.submissionArtifact.instructionPC 57 = 100 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_ret58 : Artifact.submissionArtifact.instructionPC 58 = 101 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_ret59 : Artifact.submissionArtifact.instructionPC 59 = 102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] theorem pc_ret60 : Artifact.submissionArtifact.instructionPC 60 = 103 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

def entryDest : Located :=
  ⟨148, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩

def wordPath : List Located :=
  [⟨3530, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by exact GuardInstructionWindow.get 0, by decide⟩,
   ⟨3531, .op .CALLDATALOAD, by exact GuardInstructionWindow.get 1, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3532, .push ⟨1, by decide⟩ (UInt256.ofNat 232), by exact GuardInstructionWindow.get 2, by decide⟩,
   ⟨3533, .op .SAR, by exact GuardInstructionWindow.get 3, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3534, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 4, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3535, .push ⟨3, by decide⟩ (UInt256.ofNat 2127393), by exact GuardInstructionWindow.get 5, by decide⟩,
   ⟨3536, .op .MUL, by exact GuardInstructionWindow.get 6, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3537, .op .XOR, by exact GuardInstructionWindow.get 7, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3538, .push ⟨1, by decide⟩ (UInt256.ofNat 246), by exact GuardInstructionWindow.get 8, by decide⟩,
   ⟨3539, .op .JUMPI, by exact GuardInstructionWindow.get 9, ⟨by decide, trivial, rfl⟩⟩]

def wordMissPath : List Located := wordPath ++ [entryDest]

def storePath : List Located :=
  [⟨3540, .push ⟨20, by decide⟩ (UInt256.ofNat 95383801997447390147238369573240532004699299169), by exact GuardInstructionWindow.get 10, by decide⟩,
   ⟨3541, .op .CALLDATASIZE, by exact GuardInstructionWindow.get 11, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3542, .op .SHR, by exact GuardInstructionWindow.get 12, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3543, .push ⟨20, by decide⟩ (UInt256.ofNat 802931186561056611446976448233794645126013734992), by exact GuardInstructionWindow.get 13, by decide⟩,
   ⟨3544, .op .XOR, by exact GuardInstructionWindow.get 14, ⟨by decide, trivial, rfl⟩⟩,
   ⟨3545, .push ⟨1, by decide⟩ (UInt256.ofNat 98), by exact GuardInstructionWindow.get 15, by decide⟩,
   ⟨3546, .op .JUMP, by exact GuardInstructionWindow.get 16, ⟨by decide, trivial, rfl⟩⟩,
   ⟨55, .op .JUMPDEST, by rfl, ⟨by decide, trivial, rfl⟩⟩,
   ⟨56, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨57, .op .MSTORE, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def finishPath : List Located :=
  [⟨59, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨60, .op .RETURN, by rfl, ⟨by decide, trivial, rfl⟩⟩]

def sizeCond (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (UInt256.ofNat input.size) (UInt256.ofNat 2)
/-- The arm's lead word: `calldata[0] SAR 232` (sign-extending). -/
def leadWordS (input : ByteArray) : UInt256 :=
  UInt256.sar (MachineState.readWord input 0) (UInt256.ofNat 232)
def wordCond (input : ByteArray) : UInt256 :=
  UInt256.xor (leadWordS input)
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621))
/-- The unsigned form used by `TinyGuardLogic.condition`. -/
def wordCondU (input : ByteArray) : UInt256 :=
  UInt256.xor (leadWord input)
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621))
def armEntry (input : ByteArray) : State := Execution.atPC input 4740
def fallbackState (input : ByteArray) : State := Execution.atPC input 247
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
    pc := UInt256.ofNat 101
    memory := answerMemory input
    activeWords := UInt256.ofNat 1}
def sized (input : ByteArray) : State :=
  {stored input with pc := UInt256.ofNat 102, stack := [UInt256.ofNat 32]}
def returned (input : ByteArray) : State :=
  {stored input with
    pc := UInt256.ofNat 103
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

@[simp] theorem valid_ret : Decode.isValidJumpDest submissionBytecode 98 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 55 (by rfl)
  rw [pc_ret55] at h
  exact h

private theorem valid_generic : Decode.isValidJumpDest submissionBytecode 246 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 148 (by rfl)
  rw [pc_176] at h
  exact h
/-! ### Sign-extending shift facts -/

theorem sar_toNat_small (v : UInt256) (h : v.toNat < 2 ^ 255) :
    (UInt256.sar v (UInt256.ofNat 232)).toNat = v.toNat / 2 ^ 232 := by
  unfold UInt256.sar UInt256.toSignedNat UInt256.ofSignedInt
  have h232 : (UInt256.ofNat 232).toNat = 232 := by decide
  have hs : UInt256.size = 2 ^ 256 := rfl
  rw [h232, if_neg (by norm_num)]
  simp only [hs]
  rw [if_pos (by rw [show (2:Nat) ^ 256 / 2 = 2 ^ 255 by norm_num]; exact h)]
  rw [Word.word_toNat_ofNat]
  have hv : v.toNat < 2 ^ 256 := v.val.isLt
  generalize hx : v.toNat = x at h hv ⊢
  have hlt : ((x : Int) / (2 ^ 232 : Int) % ((2 ^ 256 : Nat) : Int)).toNat < 2 ^ 256 := by
    omega
  have key : ((x : Int) / (2 ^ 232 : Int) % ((2 ^ 256 : Nat) : Int)).toNat = x / 2 ^ 232 := by
    omega
  rw [Nat.mod_eq_of_lt (by push_cast at hlt ⊢; exact hlt)]
  push_cast at key ⊢
  exact key

theorem sar_toNat_big (v : UInt256) (h : 2 ^ 255 ≤ v.toNat) :
    2 ^ 255 ≤ (UInt256.sar v (UInt256.ofNat 232)).toNat := by
  unfold UInt256.sar UInt256.toSignedNat UInt256.ofSignedInt
  have h232 : (UInt256.ofNat 232).toNat = 232 := by decide
  have hs : UInt256.size = 2 ^ 256 := rfl
  have hv : v.toNat < 2 ^ 256 := v.val.isLt
  rw [h232, if_neg (by norm_num)]
  simp only [hs]
  rw [if_neg (by rw [show (2:Nat) ^ 256 / 2 = 2 ^ 255 by norm_num]; omega)]
  rw [Word.word_toNat_ofNat]
  generalize hx : v.toNat = x at h hv
  have key : 2 ^ 255 ≤ (((x : Int) - ((2 ^ 256 : Nat) : Int)) / (2 ^ 232 : Int) %
      ((2 ^ 256 : Nat) : Int)).toNat := by
    omega
  have hlt : (((x : Int) - ((2 ^ 256 : Nat) : Int)) / (2 ^ 232 : Int) %
      ((2 ^ 256 : Nat) : Int)).toNat < 2 ^ 256 := by
    omega
  rw [Nat.mod_eq_of_lt (by push_cast at hlt ⊢; exact hlt)]
  push_cast at key ⊢
  exact key

private theorem word_toNat_mulG (x y : UInt256) :
    (x * y).toNat = (x.toNat * y.toNat) % 2 ^ 256 := by
  show (x.val * y.val).val = _
  rw [Fin.val_mul]
  rfl

private theorem mul_size_toNat' (input : ByteArray) (hfit : CalldataFits input) :
    (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621)).toNat =
      input.size * 0x207621 := by
  have hs : input.size < 2 ^ 64 := hfit
  have hm : (UInt256.mul (UInt256.ofNat input.size) (UInt256.ofNat 0x207621)).toNat =
      ((UInt256.ofNat input.size).toNat * (UInt256.ofNat 0x207621).toNat) % 2 ^ 256 :=
    word_toNat_mulG _ _
  rw [hm, Word.word_toNat_ofNat, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hs (by norm_num)),
    Nat.mod_eq_of_lt (by norm_num : (0x207621 : Nat) < 2 ^ 256)]
  apply Nat.mod_eq_of_lt
  have h1 : input.size * 0x207621 < 2 ^ 64 * 0x207621 :=
    Nat.mul_lt_mul_of_pos_right hs (by norm_num)
  exact lt_of_lt_of_le h1 (by norm_num)

theorem leadWordS_eq (input : ByteArray)
    (h : (MachineState.readWord input 0).toNat < 2 ^ 255) : leadWordS input = leadWord input := by
  apply Word.word_ext
  rw [leadWordS, sar_toNat_small _ h, leadWord, Word.shiftRight_toNat _ (by decide),
    Nat.shiftRight_eq_div_pow]

theorem wordCond_eq_U (input : ByteArray)
    (h : (MachineState.readWord input 0).toNat < 2 ^ 255) : wordCond input = wordCondU input := by
  rw [wordCond, wordCondU, leadWordS_eq input h]

/-- A zero sign-extended word test forces a clear top bit. -/
theorem small_of_wordCond (input : ByteArray) (hfit : CalldataFits input)
    (hz : wordCond input = 0) : (MachineState.readWord input 0).toNat < 2 ^ 255 := by
  by_contra hn
  have hbig := sar_toNat_big _ (Nat.le_of_not_lt hn)
  have heq := congrArg UInt256.toNat ((KnownInputLogic.wordXor_eq_zero_iff _ _).mp hz)
  rw [mul_size_toNat' input hfit] at heq
  change (leadWordS input).toNat = _ at heq
  have hs : input.size < 2 ^ 64 := hfit
  unfold leadWordS at heq
  omega

/-- The top bit is clear exactly when the unsigned lead word is below `2^23`. -/
theorem small_of_lead (input : ByteArray) (h : (leadWord input).toNat < 2 ^ 23) :
    (MachineState.readWord input 0).toNat < 2 ^ 255 := by
  rw [leadWord, Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow] at h
  omega

theorem lead_of_small (input : ByteArray)
    (h : (MachineState.readWord input 0).toNat < 2 ^ 255) : (leadWord input).toNat < 2 ^ 23 := by
  rw [leadWord, Word.shiftRight_toNat _ (by decide), Nat.shiftRight_eq_div_pow]
  omega

/-- The sign-extended arm test can only match inputs shorter than four bytes. -/
theorem size_lt_four_of_wordCond (input : ByteArray) (hfit : CalldataFits input)
    (hz : wordCond input = 0) : input.size < 4 := by
  have hsmall := small_of_wordCond input hfit hz
  rw [wordCond_eq_U input hsmall] at hz
  have heq := congrArg UInt256.toNat ((KnownInputLogic.wordXor_eq_zero_iff _ _).mp hz)
  rw [mul_size_toNat' input hfit] at heq
  have hl := lead_of_small input hsmall
  rw [heq] at hl
  by_contra hn
  have hk : 4 * 0x207621 ≤ input.size * 0x207621 := Nat.mul_le_mul_right _ (by omega)
  omega

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

def wordHead : List Located := wordPath.take 3
def wordCalc : List Located := (wordPath.drop 4).take 5
def wordBranch : Located :=
  ⟨3539, .op .JUMPI, by exact GuardInstructionWindow.get 9, ⟨by decide, trivial, rfl⟩⟩
def wordLoaded (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4744
    stack := [UInt256.ofNat 232, MachineState.readWord input 0] }
def wordShifted (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4745
    stack := [leadWordS input] }
def wordTested (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4754
    stack := [UInt256.ofNat 246, wordCond input] }

private theorem run_word_head (input : ByteArray) :
    DataStepper.runLocatedBlock wordHead (armEntry input) = some (wordLoaded input) := by
  simp [wordHead, wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    armEntry, wordLoaded, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat]
private theorem run_word_calc (input : ByteArray) :
    DataStepper.runLocatedBlock wordCalc (wordShifted input) = some (wordTested input) := by
  simp [wordCalc, wordPath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    wordShifted, wordTested, wordCond, Execution.atPC, initialState, UInt256.succ,
    Word.ofNat_add_mod, Word.word_toNat_ofNat, mul_op, RawExpressionAC.mul_comm, RawExpressionAC.xor_comm]

private def gasSteps_sar (input : ByteArray) : GasSteps (wordLoaded input) (wordShifted input) := by
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3533 .SAR
    (by exact GuardInstructionWindow.get 3) (by decide) trivial
  have hp : (wordLoaded input).pc.toNat = Artifact.submissionArtifact.instructionPC 3533 := by
    rw [pc_4098]; rfl
  have hop : (wordLoaded input).decodedOp = some .SAR :=
    Artifact.submissionArtifact.state_decodedOp_of (wordLoaded input) 3533 rfl hp .SAR none hd rfl
  have g := sarStep (s := wordLoaded input) (shift := UInt256.ofNat 232)
    (value := MachineState.readWord input 0) (rest := []) hop rfl
    (by show 2 + Operation.pushArity .SAR ≤ 1024 + Operation.popArity .SAR; decide) rfl
    deployAddress_not_precompile
  have ht : { wordLoaded input with
      stack := UInt256.sar (MachineState.readWord input 0) (UInt256.ofNat 232) :: [],
      pc := (wordLoaded input).pc.succ } = wordShifted input := by
    simp [wordLoaded, wordShifted, leadWordS, initialState, Word.succ_ofNat_mod,
      Word.word_toNat_ofNat]
  exact ht ▸ g

private def soundW (path : List Located) {s t : State}
    (h : DataStepper.runLocatedBlock path s = some t)
    (hc : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hf : s.fork = .Osaka := by rfl) (hr : s.halt = .Running := by rfl)
    (hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by exact deployAddress_not_precompile) :
    GasSteps s t :=
  DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path hc hf h hr hn

private def gasSteps_word_prefix (input : ByteArray) :
    GasSteps (armEntry input) (wordTested input) :=
  (soundW wordHead (run_word_head input)).trans
    ((gasSteps_sar input).trans (soundW wordCalc (run_word_calc input)))

theorem run_word_miss (input : ByteArray) (hm : wordCond input ≠ 0) :
    DataStepper.runLocatedBlock [wordBranch, entryDest] (wordTested input) =
      some (fallbackState input) := by
  have hbranch : DataStepper.runLocatedBlock [wordBranch] (wordTested input) =
      some (PatternedScan.stS input 246 []) :=
    PatternedScan.blockOfS wordBranch
      (PatternedScan.pcFactS input 3539 4754 [UInt256.ofNat 246, wordCond input] (by norm_num) pc_4104)
      (PatternedScan.stepS_jumpi_taken input 4754 246 (UInt256.ofNat 246) (wordCond input) []
        (by simp) (by norm_num) rfl (by simpa using true_of_ne_zero (wordCond input) hm) valid_generic)
  have hd : DataStepper.runLocatedBlock [entryDest] (PatternedScan.stS input 246 []) =
      some (fallbackState input) := by
    exact PatternedScan.blockOfS entryDest
      (PatternedScan.pcFactS input 148 246 [] (by norm_num) pc_176)
      (PatternedScan.stepS_jumpdest input 246 [] (by simp) (by norm_num))
  exact DataStepper.runLocatedBlock_append [wordBranch] [entryDest]
    _ _ _ hbranch rfl hd

theorem run_word_hit (input : ByteArray) (hm : wordCond input = 0) :
    DataStepper.runLocatedBlock [wordBranch] (wordTested input) = some (Execution.atPC input 4755) := by
  have ht : ¬ UInt256.isTrue (wordCond input) := by rw [hm]; decide
  exact PatternedScan.blockOfS wordBranch
    (PatternedScan.pcFactS input 3539 4754 [UInt256.ofNat 246, wordCond input] (by norm_num) pc_4104)
    (PatternedScan.stepS_jumpi_fall input 4754 (UInt256.ofNat 246) (wordCond input) []
      (by simp) (by norm_num) ht)

theorem run_store (input : ByteArray) :
    DataStepper.runLocatedBlock storePath (Execution.atPC input 4755) = some (stored input) := by
  simp [storePath, DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    Execution.atPC, initialState, stored, answerMemory, answerBytes, answerWord, valid_ret,
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
  (gasSteps_word_prefix input).trans (sound [wordBranch, entryDest] (run_word_miss input hw))

def gasSteps_hit (input : ByteArray) (hw : wordCond input = 0) :
    GasSteps (armEntry input) (returned input) := by
  have gw := (gasSteps_word_prefix input).trans (sound [wordBranch] (run_word_hit input hw))
  have gs := sound storePath (run_store input)
  have hd := Artifact.submissionArtifact.decodeAt_op_index 58 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (stored input).pc.toNat = Artifact.submissionArtifact.instructionPC 58 := by
    rw [pc_ret58]; rfl
  have hop : (stored input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (stored input) 58 rfl hp .MSIZE none hd rfl
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
  have hwU : wordCondU input = 0 := by
    rw [← wordCond_eq_U input (small_of_wordCond input hfit hw)]
    exact hw
  have hc : condition input = 0 := by
    change UInt256.lor (wordCondU input) (sizeCond input) = 0
    rw [hwU, hs]
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
  subst input
  have hc := condition_abc
  change UInt256.lor (wordCondU AbcInputData.abcInput) (sizeCond AbcInputData.abcInput) = 0 at hc
  obtain ⟨hw, hs⟩ := (KnownInputLogic.wordOr_eq_zero_iff _ _).mp hc
  have hlead : (leadWord AbcInputData.abcInput).toNat < 2 ^ 23 := by
    rw [leadWord_abc, Word.word_toNat_ofNat]
    norm_num
  have hwS : wordCond AbcInputData.abcInput = 0 := by
    rw [wordCond_eq_U _ (small_of_lead _ hlead)]
    exact hw
  exact correct_hit _ hfit hs hwS entryPrefix

theorem wordCond_empty : wordCond ByteArray.empty = 0 := by
  have hc := condition_empty
  change UInt256.lor (wordCondU ByteArray.empty) (sizeCond ByteArray.empty) = 0 at hc
  obtain ⟨hw, _⟩ := (KnownInputLogic.wordOr_eq_zero_iff _ _).mp hc
  have hlead : (leadWord ByteArray.empty).toNat < 2 ^ 23 := by
    rw [leadWord_empty]
    decide
  rw [wordCond_eq_U _ (small_of_lead _ hlead)]
  exact hw

theorem correct_empty (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = ByteArray.empty)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (armEntry input)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  subst input
  have hc := condition_empty
  change UInt256.lor (wordCondU ByteArray.empty) (sizeCond ByteArray.empty) = 0 at hc
  obtain ⟨hw, hs⟩ := (KnownInputLogic.wordOr_eq_zero_iff _ _).mp hc
  have hlead : (leadWord ByteArray.empty).toNat < 2 ^ 23 := by
    rw [leadWord_empty]
    decide
  have hwS : wordCond ByteArray.empty = 0 := by
    rw [wordCond_eq_U _ (small_of_lead _ hlead)]
    exact hw
  exact correct_hit _ hfit hs hwS entryPrefix

#print axioms correct_hit
#print axioms gasSteps_miss
end Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
