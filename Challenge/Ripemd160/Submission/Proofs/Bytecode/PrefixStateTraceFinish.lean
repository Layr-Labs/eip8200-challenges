import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-! Compact four-block checked prefix. Later expected words are derived only
from earlier words that have already been proved equal to their constants.
The scalar byte mask replaces the discarded message pointer on the stack.
Every mismatch drops that mask in the H1 installer; all matches install H4. -/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

private def frame (s : State) (input : ByteArray) (pc : Nat) : State :=
  { s with
    pc := UInt256.ofNat pc
    stack := [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

def byteMask : UInt256 := UInt256.ofNat 29061543965444064733758992315905984716114819680788219994216805398064471752768

private def maskFrame (s : State) (input : ByteArray) (pc : Nat) : State :=
  {s with pc := UInt256.ofNat pc,
    stack := [byteMask, UInt256.ofNat 102, DriverTrace.blockOffsetWord 0, Padding.paddedWord input]}

def entry (s : State) (input : ByteArray) : State := frame s input 4986
def rungEntry (s : State) (input : ByteArray) : State := frame s input 5027
def hit2Entry (s : State) (input : ByteArray) : State := maskFrame s input 5139
def hit1Entry (s : State) (input : ByteArray) : State := maskFrame s input 5186

def check2Entry (s : State) (input : ByteArray) : State := maskFrame s input 5036
def check3Entry (s : State) (input : ByteArray) : State := maskFrame s input 5054
def check4Entry (s : State) (input : ByteArray) : State := maskFrame s input 5073
def check5Entry (s : State) (input : ByteArray) : State := maskFrame s input 5087
def check6Entry (s : State) (input : ByteArray) : State := maskFrame s input 5102
def check7Entry (s : State) (input : ByteArray) : State := maskFrame s input 5117

/-- The generic compression target of the guard is a valid jump destination. -/
theorem jumpDest_generic : Decode.isValidJumpDest submissionBytecode 464 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 272 = 464 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 272 (by rfl)
  rw [hpc] at h
  exact h

/-- The `H1` install entry is a valid jump destination. -/
theorem jumpDest_hit1 : Decode.isValidJumpDest submissionBytecode 5186 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4196 = 5186 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4196 (by rfl)
  rw [hpc] at h
  exact h

/-- The driver's `102` continuation is a valid jump destination. -/
theorem jumpDest_driver : Decode.isValidJumpDest submissionBytecode 102 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 64 = 102 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 64 (by rfl)
  rw [hpc] at h
  exact h

/-- The `H1` stores return to the driver's `102` continuation. -/
theorem run_hit1 (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.hitPath
      (hit1Entry s input) =
      some (PrefixStateMemory.resultState s input 0) := by
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hitPath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hit1Entry, maskFrame, PrefixStateMemory.resultState,
      PrefixStateMemory.hashMemory, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash, FastEmptyBlock.emptyActiveWords,
      hcode, hrun, jumpDest_driver,
      PrefixStatePaths.pc4126,
      PrefixStatePaths.pc4127,
      PrefixStatePaths.pc4128,
      PrefixStatePaths.pc4129,
      PrefixStatePaths.pc4130,
      PrefixStatePaths.pc4131,
      PrefixStatePaths.pc4132,
      PrefixStatePaths.pc4133,
      PrefixStatePaths.pc4134,
      PrefixStatePaths.pc4135,
      PrefixStatePaths.pc4136,
      PrefixStatePaths.pc4137,
      PrefixStatePaths.pc4138,
      PrefixStatePaths.pc4139,
      PrefixStatePaths.pc4140,
      PrefixStatePaths.pc4141,
      PrefixStatePaths.pc4142,
      PrefixStatePaths.pc4143,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- The `H2` stores return to the driver's `102` continuation with the
block-1 offset replacing the block-0 offset. -/
theorem run_hit2 (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.hit2Path
      (hit2Entry s input) =
      some (PrefixStateMemory.resultState2 s input) := by
  have hbo : DriverTrace.blockOffsetWord 3 = UInt256.ofNat 192 := rfl
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hit2Path,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hit2Entry, maskFrame, PrefixStateMemory.resultState2,
      PrefixStateMemory.hashMemory2, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash2, FastEmptyBlock.emptyActiveWords,
      hcode, hrun, jumpDest_driver, hbo, List.exchange,
      PrefixStatePaths.pc4105,
      PrefixStatePaths.pc4106,
      PrefixStatePaths.pc4107,
      PrefixStatePaths.pc4108,
      PrefixStatePaths.pc4109,
      PrefixStatePaths.pc4110,
      PrefixStatePaths.pc4111,
      PrefixStatePaths.pc4112,
      PrefixStatePaths.pc4113,
      PrefixStatePaths.pc4114,
      PrefixStatePaths.pc4115,
      PrefixStatePaths.pc4116,
      PrefixStatePaths.pc4117,
      PrefixStatePaths.pc4118,
      PrefixStatePaths.pc4119,
      PrefixStatePaths.pc4120,
      PrefixStatePaths.pc4121,
      PrefixStatePaths.pc4122,
      PrefixStatePaths.pc4123,
      PrefixStatePaths.pc4124,
      PrefixStatePaths.pc4125,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- Word-1 guard on a match: the `JUMPI` is not taken. -/
theorem run_secondCompare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 32 =
      PatternedWordData.expectedWordAt 1)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.secondComparePath
      (entry s input) = some (rungEntry s input) := by
  have hzero : UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 1)
      (MachineState.readWord input 32) = 0 := by
    calc
      UInt256.xor (PatternedWordData.expectedWordAt 1)
          (MachineState.readWord input 32) =
        UInt256.xor (MachineState.readWord input 32)
          (PatternedWordData.expectedWordAt 1) := BooleanSelect.xor_comm _ _
      _ = 0 := hzero
  have hcond : (UInt256.xor (PatternedWordData.expectedWordAt 1)
      (MachineState.readWord input 32)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906)
        (MachineState.readWord input 32)).toNat = 0 := by
    have hconst :
        (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906 : UInt256) =
          (75898346434861812577553744355519055536350986179947755549958789636940356975906 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_1] using hcond
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.secondComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entry, rungEntry, frame, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
      BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4087,
      PrefixStatePaths.pc4088,
      PrefixStatePaths.pc4089,
      PrefixStatePaths.pc4090,
      PrefixStatePaths.pc4091,
      PrefixStatePaths.pc4092,
      jumpDest_generic,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-1 guard on a mismatch: the `JUMPI` is taken. -/
theorem run_secondCompare_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 32 ≠
      PatternedWordData.expectedWordAt 1)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.secondComparePath
      (entry s input) = some (DriverTrace.compressEntry s input 0) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 1)
      (MachineState.readWord input 32)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 1)
        (MachineState.readWord input 32) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 32)
      (PatternedWordData.expectedWordAt 1)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 1)
      (MachineState.readWord input 32)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 1)
        (MachineState.readWord input 32) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906)
        (MachineState.readWord input 32)).toNat ≠ 0 := by
    have hconst :
        (UInt256.ofNat 75898346434861812577553744355519055536350986179947755549958789636940356975906 : UInt256) =
          (75898346434861812577553744355519055536350986179947755549958789636940356975906 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_1] using hcond'
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.secondComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      entry, DriverTrace.compressEntry, frame, hcalldata, hcode, hrun,
      htrue, htrue', hcond, hcond', hcondLit, BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4087,
      PrefixStatePaths.pc4088,
      PrefixStatePaths.pc4089,
      PrefixStatePaths.pc4090,
      PrefixStatePaths.pc4091,
      PrefixStatePaths.pc4092,
      jumpDest_generic,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

theorem byteMask_construct :
    UInt256.ofNat 64 * (UInt256.lnot (UInt256.ofNat 0) / UInt256.ofNat 255) = byteMask := by decide

#print axioms byteMask_construct

theorem xor_nat_zero_iff (a b : UInt256) : (UInt256.xor a b).toNat = 0 ↔ a = b := by
  constructor
  · intro h
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using h
  · intro h
    have hz := (KnownInputLogic.wordXor_eq_zero_iff a b).2 h
    rw [hz]
    rfl

theorem run_prepare (s : State) (input : ByteArray) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactPreparePath (rungEntry s input) =
      some (check2Entry s input) := by
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactPreparePath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, rungEntry, check2Entry, frame, maskFrame, hrun, byteMask_construct,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

def expected2 (b : UInt256) : UInt256 := UInt256.xor byteMask (UInt256.xor (UInt256.land byteMask b + UInt256.land byteMask b) b)

theorem expected2_value : expected2 (PatternedWordData.expectedWordAt 0) =
    PatternedWordData.expectedWordAt 2 := by decide

#print axioms expected2_value

theorem run_check2_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hword : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord2Path (check2Entry s input) =
      some (check3Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 64) (PatternedWordData.expectedWordAt 2)).toNat = 0 := (xor_nat_zero_iff _ _).2 hword
  have hexpected := expected2_value
  unfold expected2 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord2Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check2Entry, check3Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

theorem run_check2_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hword : MachineState.readWord input 64 ≠ PatternedWordData.expectedWordAt 2)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord2Path (check2Entry s input) =
      some (hit1Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 64) (PatternedWordData.expectedWordAt 2)).toNat ≠ 0 := fun hz => hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected := expected2_value
  unfold expected2 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord2Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check2Entry, hit1Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

def expected3 (b : UInt256) : UInt256 := UInt256.xor byteMask (UInt256.xor (UInt256.land byteMask b + UInt256.land byteMask b) b)

theorem expected3_value : expected3 (PatternedWordData.expectedWordAt 1) =
    PatternedWordData.expectedWordAt 3 := by decide

#print axioms expected3_value

theorem run_check3_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hword : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord3Path (check3Entry s input) =
      some (check4Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 96) (PatternedWordData.expectedWordAt 3)).toNat = 0 := (xor_nat_zero_iff _ _).2 hword
  have hexpected := expected3_value
  unfold expected3 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord3Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check3Entry, check4Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

theorem run_check3_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hword : MachineState.readWord input 96 ≠ PatternedWordData.expectedWordAt 3)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord3Path (check3Entry s input) =
      some (hit1Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 96) (PatternedWordData.expectedWordAt 3)).toNat ≠ 0 := fun hz => hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected := expected3_value
  unfold expected3 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord3Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check3Entry, hit1Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

def expected4 (b : UInt256) : UInt256 := UInt256.xor (byteMask + byteMask) b

theorem expected4_value : expected4 (PatternedWordData.expectedWordAt 0) =
    PatternedWordData.expectedWordAt 4 := by decide

#print axioms expected4_value

theorem run_check4_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hword : MachineState.readWord input 128 = PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord4Path (check4Entry s input) =
      some (check5Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 128) (PatternedWordData.expectedWordAt 4)).toNat = 0 := (xor_nat_zero_iff _ _).2 hword
  have hexpected := expected4_value
  unfold expected4 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord4Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check4Entry, check5Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

theorem run_check4_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hword : MachineState.readWord input 128 ≠ PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord4Path (check4Entry s input) =
      some (hit1Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 128) (PatternedWordData.expectedWordAt 4)).toNat ≠ 0 := fun hz => hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected := expected4_value
  unfold expected4 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord4Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check4Entry, hit1Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

def expected5 (b : UInt256) : UInt256 := UInt256.xor (byteMask + byteMask) b

theorem expected5_value : expected5 (PatternedWordData.expectedWordAt 1) =
    PatternedWordData.expectedWordAt 5 := by decide

#print axioms expected5_value

theorem run_check5_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hword : MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord5Path (check5Entry s input) =
      some (check6Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 160) (PatternedWordData.expectedWordAt 5)).toNat = 0 := (xor_nat_zero_iff _ _).2 hword
  have hexpected := expected5_value
  unfold expected5 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord5Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check5Entry, check6Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

theorem run_check5_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1)
    (hword : MachineState.readWord input 160 ≠ PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord5Path (check5Entry s input) =
      some (hit1Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 160) (PatternedWordData.expectedWordAt 5)).toNat ≠ 0 := fun hz => hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected := expected5_value
  unfold expected5 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord5Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check5Entry, hit1Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

def expected6 (b : UInt256) : UInt256 := UInt256.xor (byteMask + byteMask) b

theorem expected6_value : expected6 (PatternedWordData.expectedWordAt 2) =
    PatternedWordData.expectedWordAt 6 := by decide

#print axioms expected6_value

theorem run_check6_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2)
    (hword : MachineState.readWord input 192 = PatternedWordData.expectedWordAt 6)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord6Path (check6Entry s input) =
      some (check7Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 192) (PatternedWordData.expectedWordAt 6)).toNat = 0 := (xor_nat_zero_iff _ _).2 hword
  have hexpected := expected6_value
  unfold expected6 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord6Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check6Entry, check7Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

theorem run_check6_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2)
    (hword : MachineState.readWord input 192 ≠ PatternedWordData.expectedWordAt 6)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord6Path (check6Entry s input) =
      some (hit1Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 192) (PatternedWordData.expectedWordAt 6)).toNat ≠ 0 := fun hz => hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected := expected6_value
  unfold expected6 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord6Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check6Entry, hit1Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

def expected7 (b : UInt256) : UInt256 := UInt256.xor (UInt256.ofNat 99006248207) (UInt256.xor (byteMask + byteMask) b)

theorem expected7_value : expected7 (PatternedWordData.expectedWordAt 3) =
    PatternedWordData.expectedWordAt 7 := by decide

#print axioms expected7_value

theorem run_check7_hit (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3)
    (hword : MachineState.readWord input 224 = PatternedWordData.expectedWordAt 7)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord7Path (check7Entry s input) =
      some (hit2Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 224) (PatternedWordData.expectedWordAt 7)).toNat = 0 := (xor_nat_zero_iff _ _).2 hword
  have hexpected := expected7_value
  unfold expected7 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord7Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check7Entry, hit2Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

theorem run_check7_miss (s : State) (input : ByteArray)
    (hbase : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3)
    (hword : MachineState.readWord input 224 ≠ PatternedWordData.expectedWordAt 7)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.compactWord7Path (check7Entry s input) =
      some (hit1Entry s input) := by
  have hcond : (UInt256.xor (MachineState.readWord input 224) (PatternedWordData.expectedWordAt 7)).toNat ≠ 0 := fun hz => hword ((xor_nat_zero_iff _ _).1 hz)
  have hexpected := expected7_value
  unfold expected7 at hexpected
  simp (config := {maxSteps := 500000})
    [PrefixStatePaths.compactWord7Path, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, check7Entry, hit1Entry, maskFrame, hcalldata, hcode, hrun,
      hbase, hexpected, hcond, UInt256.isTrue, jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat, Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, List.getElem?_cons_zero]

private def gasStepsBlock (path : List PrefixStatePaths.Located) (s t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork hresult hrun hnp

/-- Any frame state carries the environment facts of `s`. -/
private def frameBlock (path : List PrefixStatePaths.Located) (s : State) (input : ByteArray)
    (pc : Nat) (t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path (frame s input pc) = some t) :
    Challenge.EvmProof.GasSteps (frame s input pc) t :=
  gasStepsBlock path (frame s input pc) t
    (by simpa [frame] using hcode)
    (by simpa [frame, State.fork] using hfork)
    hresult
    (by simpa [frame] using hrun)
    (by simpa [frame] using hnp)

private def maskBlock (path : List PrefixStatePaths.Located) (s : State) (input : ByteArray)
    (pc : Nat) (t : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hresult : Challenge.EvmProof.Stepper.runLocatedBlock path (maskFrame s input pc) = some t) :
    Challenge.EvmProof.GasSteps (maskFrame s input pc) t :=
  gasStepsBlock path (maskFrame s input pc) t
    (by simpa [maskFrame] using hcode)
    (by simpa [maskFrame, State.fork] using hfork)
    hresult
    (by simpa [maskFrame] using hrun)
    (by simpa [maskFrame] using hnp)

def gasSteps_finish (s : State) (input : ByteArray)
    (hw0 : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s input)
      (if MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1 then
        (if PrefixStateModel.Matched2 input then PrefixStateMemory.resultState2 s input
          else PrefixStateMemory.resultState s input 0)
      else DriverTrace.compressEntry s input 0) := by
  have ghit1 : GasSteps (hit1Entry s input) (PrefixStateMemory.resultState s input 0) :=
    maskBlock PrefixStatePaths.hitPath s input 5186 _ hcode hfork hrun hnp (run_hit1 s input hcode hrun)
  have ghit2 : GasSteps (hit2Entry s input) (PrefixStateMemory.resultState2 s input) :=
    maskBlock PrefixStatePaths.hit2Path s input 5139 _ hcode hfork hrun hnp (run_hit2 s input hcode hrun)
  by_cases hw1 : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1
  · rw [if_pos hw1]
    have gsecond : GasSteps (entry s input) (rungEntry s input) :=
      frameBlock PrefixStatePaths.secondComparePath s input 4986 _ hcode hfork hrun hnp
        (run_secondCompare_hit s input hw1 hcalldata hcode hrun)
    have gprep : GasSteps (rungEntry s input) (check2Entry s input) :=
      frameBlock PrefixStatePaths.compactPreparePath s input 5027 _ hcode hfork hrun hnp
        (run_prepare s input hrun)
    by_cases hw2 : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2
    · have g2 : GasSteps (check2Entry s input) (check3Entry s input) :=
        maskBlock PrefixStatePaths.compactWord2Path s input 5036 _ hcode hfork hrun hnp
          (run_check2_hit s input hw0 hw2 hcalldata hcode hrun)
      by_cases hw3 : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3
      · have g3 : GasSteps (check3Entry s input) (check4Entry s input) :=
          maskBlock PrefixStatePaths.compactWord3Path s input 5054 _ hcode hfork hrun hnp
            (run_check3_hit s input hw1 hw3 hcalldata hcode hrun)
        by_cases hw4 : MachineState.readWord input 128 = PatternedWordData.expectedWordAt 4
        · have g4 : GasSteps (check4Entry s input) (check5Entry s input) :=
            maskBlock PrefixStatePaths.compactWord4Path s input 5073 _ hcode hfork hrun hnp
              (run_check4_hit s input hw0 hw4 hcalldata hcode hrun)
          by_cases hw5 : MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5
          · have g5 : GasSteps (check5Entry s input) (check6Entry s input) :=
              maskBlock PrefixStatePaths.compactWord5Path s input 5087 _ hcode hfork hrun hnp
                (run_check5_hit s input hw1 hw5 hcalldata hcode hrun)
            by_cases hw6 : MachineState.readWord input 192 = PatternedWordData.expectedWordAt 6
            · have g6 : GasSteps (check6Entry s input) (check7Entry s input) :=
                maskBlock PrefixStatePaths.compactWord6Path s input 5102 _ hcode hfork hrun hnp
                  (run_check6_hit s input hw2 hw6 hcalldata hcode hrun)
              by_cases hw7 : MachineState.readWord input 224 = PatternedWordData.expectedWordAt 7
              · have g7 : GasSteps (check7Entry s input) (hit2Entry s input) :=
                  maskBlock PrefixStatePaths.compactWord7Path s input 5117 _ hcode hfork hrun hnp
                    (run_check7_hit s input hw3 hw7 hcalldata hcode hrun)
                rw [if_pos ⟨hw2, hw3, hw4, hw5, hw6, hw7⟩]
                exact gsecond.trans (gprep.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (ghit2))))))))
              · rw [if_neg (fun h => hw7 h.2.2.2.2.2)]
                have gm : GasSteps (check7Entry s input) (hit1Entry s input) :=
                  maskBlock PrefixStatePaths.compactWord7Path s input 5117 _ hcode hfork hrun hnp
                    (run_check7_miss s input hw3 hw7 hcalldata hcode hrun)
                exact gsecond.trans (gprep.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (gm.trans (ghit1))))))))
            · rw [if_neg (fun h => hw6 h.2.2.2.2.1)]
              have gm : GasSteps (check6Entry s input) (hit1Entry s input) :=
                maskBlock PrefixStatePaths.compactWord6Path s input 5102 _ hcode hfork hrun hnp
                  (run_check6_miss s input hw2 hw6 hcalldata hcode hrun)
              exact gsecond.trans (gprep.trans (g2.trans (g3.trans (g4.trans (g5.trans (gm.trans (ghit1)))))))
          · rw [if_neg (fun h => hw5 h.2.2.2.1)]
            have gm : GasSteps (check5Entry s input) (hit1Entry s input) :=
              maskBlock PrefixStatePaths.compactWord5Path s input 5087 _ hcode hfork hrun hnp
                (run_check5_miss s input hw1 hw5 hcalldata hcode hrun)
            exact gsecond.trans (gprep.trans (g2.trans (g3.trans (g4.trans (gm.trans (ghit1))))))
        · rw [if_neg (fun h => hw4 h.2.2.1)]
          have gm : GasSteps (check4Entry s input) (hit1Entry s input) :=
            maskBlock PrefixStatePaths.compactWord4Path s input 5073 _ hcode hfork hrun hnp
              (run_check4_miss s input hw0 hw4 hcalldata hcode hrun)
          exact gsecond.trans (gprep.trans (g2.trans (g3.trans (gm.trans (ghit1)))))
      · rw [if_neg (fun h => hw3 h.2.1)]
        have gm : GasSteps (check3Entry s input) (hit1Entry s input) :=
          maskBlock PrefixStatePaths.compactWord3Path s input 5054 _ hcode hfork hrun hnp
            (run_check3_miss s input hw1 hw3 hcalldata hcode hrun)
        exact gsecond.trans (gprep.trans (g2.trans (gm.trans (ghit1))))
    · rw [if_neg (fun h => hw2 h.1)]
      have gm : GasSteps (check2Entry s input) (hit1Entry s input) :=
        maskBlock PrefixStatePaths.compactWord2Path s input 5036 _ hcode hfork hrun hnp
          (run_check2_miss s input hw0 hw2 hcalldata hcode hrun)
      exact gsecond.trans (gprep.trans (gm.trans (ghit1)))
  · rw [if_neg hw1]
    exact frameBlock PrefixStatePaths.secondComparePath s input 4986 _ hcode hfork hrun hnp
      (run_secondCompare_miss s input hw1 hcalldata hcode hrun)

#print axioms gasSteps_finish
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish
