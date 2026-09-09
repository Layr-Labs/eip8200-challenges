import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# Checked-prefix finish: word-1 guard, the depth-4 ladder rung, and the installs

After the word-0 match the dispatcher checks calldata word 1.  On a match it
falls into the depth-4 rung, which checks words 2 through 7: if all match it
installs `H4` and returns to the driver with block 3 consumed
(`resultState2`, a legacy interface name); otherwise it jumps to the depth-1 install of `H1`
(`resultState`).  A word-1 mismatch goes to the generic compressor.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

private def frame (s : State) (input : ByteArray) (pc : Nat) : State :=
  { s with
    pc := UInt256.ofNat pc
    stack := [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

/-- Entry at the second word comparison in the checked prefix. -/
def entry (s : State) (input : ByteArray) : State := frame s input 4999

/-- Entry at the depth-4 rung (word-2 comparison). -/
def rungEntry (s : State) (input : ByteArray) : State := frame s input 5040

/-- Entry at the word-3 comparison. -/
def fourthEntry (s : State) (input : ByteArray) : State := frame s input 5081

/-- Entry at the `H2` install after both rung words matched. -/
def hit2Entry (s : State) (input : ByteArray) : State := frame s input 5286

def word4Entry (s : State) (input : ByteArray) : State := frame s input 5122

def word5Entry (s : State) (input : ByteArray) : State := frame s input 5163

def word6Entry (s : State) (input : ByteArray) : State := frame s input 5204

def word7Entry (s : State) (input : ByteArray) : State := frame s input 5245

/-- Entry at the `H1` install (`JUMPDEST` target of the rung's guards). -/
def hit1Entry (s : State) (input : ByteArray) : State := frame s input 5333

/-- The generic compression target of the guard is a valid jump destination. -/
theorem jumpDest_generic : Decode.isValidJumpDest submissionBytecode 464 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 272 = 464 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 272 (by rfl)
  rw [hpc] at h
  exact h

/-- The `H1` install entry is a valid jump destination. -/
theorem jumpDest_hit1 : Decode.isValidJumpDest submissionBytecode 5333 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4158 = 5333 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4158 (by rfl)
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
      hit1Entry, frame, PrefixStateMemory.resultState,
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

/-- The `H4` stores return to the driver's `102` continuation with the
block-3 offset replacing the block-0 offset. -/
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
      hit2Entry, frame, PrefixStateMemory.resultState2,
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

/-- Word-2 guard on a match: the `JUMPI` is not taken. -/
theorem run_thirdCompare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 64 =
      PatternedWordData.expectedWordAt 2)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.thirdComparePath
      (rungEntry s input) = some (fourthEntry s input) := by
  have hzero : UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 2)
      (MachineState.readWord input 64) = 0 := by
    calc
      UInt256.xor (PatternedWordData.expectedWordAt 2)
          (MachineState.readWord input 64) =
        UInt256.xor (MachineState.readWord input 64)
          (PatternedWordData.expectedWordAt 2) := BooleanSelect.xor_comm _ _
      _ = 0 := hzero
  have hcond : (UInt256.xor (PatternedWordData.expectedWordAt 2)
      (MachineState.readWord input 64)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 32306037415402008934629779266198679100989968660636699671972189525809707916738)
        (MachineState.readWord input 64)).toNat = 0 := by
    have hconst :
        (UInt256.ofNat 32306037415402008934629779266198679100989968660636699671972189525809707916738 : UInt256) =
          (32306037415402008934629779266198679100989968660636699671972189525809707916738 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_2] using hcond
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.thirdComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      rungEntry, fourthEntry, frame, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
      BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4093,
      PrefixStatePaths.pc4094,
      PrefixStatePaths.pc4095,
      PrefixStatePaths.pc4096,
      PrefixStatePaths.pc4097,
      PrefixStatePaths.pc4098,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-2 guard on a mismatch: the `JUMPI` is taken. -/
theorem run_thirdCompare_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 64 ≠
      PatternedWordData.expectedWordAt 2)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.thirdComparePath
      (rungEntry s input) = some (hit1Entry s input) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 2)
      (MachineState.readWord input 64)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 2)
        (MachineState.readWord input 64) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 64)
      (PatternedWordData.expectedWordAt 2)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 2)
      (MachineState.readWord input 64)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 2)
        (MachineState.readWord input 64) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 32306037415402008934629779266198679100989968660636699671972189525809707916738)
        (MachineState.readWord input 64)).toNat ≠ 0 := by
    have hconst :
        (UInt256.ofNat 32306037415402008934629779266198679100989968660636699671972189525809707916738 : UInt256) =
          (32306037415402008934629779266198679100989968660636699671972189525809707916738 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_2] using hcond'
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.thirdComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      rungEntry, hit1Entry, frame, hcalldata, hcode, hrun,
      htrue, htrue', hcond, hcond', hcondLit, BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4093,
      PrefixStatePaths.pc4094,
      PrefixStatePaths.pc4095,
      PrefixStatePaths.pc4096,
      PrefixStatePaths.pc4097,
      PrefixStatePaths.pc4098,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-3 guard on a match: the `JUMPI` is not taken. -/
theorem run_fourthCompare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 96 =
      PatternedWordData.expectedWordAt 3)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.fourthComparePath
      (fourthEntry s input) = some (word4Entry s input) := by
  have hzero : UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 3)
      (MachineState.readWord input 96) = 0 := by
    calc
      UInt256.xor (PatternedWordData.expectedWordAt 3)
          (MachineState.readWord input 96) =
        UInt256.xor (MachineState.readWord input 96)
          (PatternedWordData.expectedWordAt 3) := BooleanSelect.xor_comm _ _
      _ = 0 := hzero
  have hcond : (UInt256.xor (PatternedWordData.expectedWordAt 3)
      (MachineState.readWord input 96)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 104505810704657832532308207549693575120876051224915683785162626763390386191714)
        (MachineState.readWord input 96)).toNat = 0 := by
    have hconst :
        (UInt256.ofNat 104505810704657832532308207549693575120876051224915683785162626763390386191714 : UInt256) =
          (104505810704657832532308207549693575120876051224915683785162626763390386191714 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_3] using hcond
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.fourthComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      fourthEntry, word4Entry, frame, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
      BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4099,
      PrefixStatePaths.pc4100,
      PrefixStatePaths.pc4101,
      PrefixStatePaths.pc4102,
      PrefixStatePaths.pc4103,
      PrefixStatePaths.pc4104,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-3 guard on a mismatch: the `JUMPI` is taken. -/
theorem run_fourthCompare_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 96 ≠
      PatternedWordData.expectedWordAt 3)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.fourthComparePath
      (fourthEntry s input) = some (hit1Entry s input) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 3)
      (MachineState.readWord input 96)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 3)
        (MachineState.readWord input 96) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 96)
      (PatternedWordData.expectedWordAt 3)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 3)
      (MachineState.readWord input 96)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 3)
        (MachineState.readWord input 96) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 104505810704657832532308207549693575120876051224915683785162626763390386191714)
        (MachineState.readWord input 96)).toNat ≠ 0 := by
    have hconst :
        (UInt256.ofNat 104505810704657832532308207549693575120876051224915683785162626763390386191714 : UInt256) =
          (104505810704657832532308207549693575120876051224915683785162626763390386191714 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_3] using hcond'
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.fourthComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      fourthEntry, hit1Entry, frame, hcalldata, hcode, hrun,
      htrue, htrue', hcond, hcond', hcondLit, BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4099,
      PrefixStatePaths.pc4100,
      PrefixStatePaths.pc4101,
      PrefixStatePaths.pc4102,
      PrefixStatePaths.pc4103,
      PrefixStatePaths.pc4104,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Lift one concrete located path to the gas-parametric EVM relation. -/
theorem run_word4Compare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 128 =
      PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.word4ComparePath
      (word4Entry s input) = some (word5Entry s input) := by
  have hzero : UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 4)
      (MachineState.readWord input 128) = 0 := by
    calc
      UInt256.xor (PatternedWordData.expectedWordAt 4)
          (MachineState.readWord input 128) =
        UInt256.xor (MachineState.readWord input 128)
          (PatternedWordData.expectedWordAt 4) := BooleanSelect.xor_comm _ _
      _ = 0 := hzero
  have hcond : (UInt256.xor (PatternedWordData.expectedWordAt 4)
      (MachineState.readWord input 128)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146)
        (MachineState.readWord input 128)).toNat = 0 := by
    have hconst :
        (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146 : UInt256) =
          (61367581353886127001238131413293229573374005415347599533452268822761471270146 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_4] using hcond
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word4ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      word4Entry, word5Entry, frame, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
      BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.widePc4105,
      PrefixStatePaths.widePc4106,
      PrefixStatePaths.widePc4107,
      PrefixStatePaths.widePc4108,
      PrefixStatePaths.widePc4109,
      PrefixStatePaths.widePc4110,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-2 guard on a mismatch: the `JUMPI` is taken. -/
theorem run_word4Compare_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 128 ≠
      PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.word4ComparePath
      (word4Entry s input) = some (hit1Entry s input) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 4)
      (MachineState.readWord input 128)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 4)
        (MachineState.readWord input 128) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 128)
      (PatternedWordData.expectedWordAt 4)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 4)
      (MachineState.readWord input 128)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 4)
        (MachineState.readWord input 128) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146)
        (MachineState.readWord input 128)).toNat ≠ 0 := by
    have hconst :
        (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146 : UInt256) =
          (61367581353886127001238131413293229573374005415347599533452268822761471270146 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_4] using hcond'
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word4ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      word4Entry, hit1Entry, frame, hcalldata, hcode, hrun,
      htrue, htrue', hcond, hcond', hcondLit, BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.widePc4105,
      PrefixStatePaths.widePc4106,
      PrefixStatePaths.widePc4107,
      PrefixStatePaths.widePc4108,
      PrefixStatePaths.widePc4109,
      PrefixStatePaths.widePc4110,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]


theorem run_word5Compare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 160 =
      PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.word5ComparePath
      (word5Entry s input) = some (word6Entry s input) := by
  have hzero : UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 5)
      (MachineState.readWord input 160) = 0 := by
    calc
      UInt256.xor (PatternedWordData.expectedWordAt 5)
          (MachineState.readWord input 160) =
        UInt256.xor (MachineState.readWord input 160)
          (PatternedWordData.expectedWordAt 5) := BooleanSelect.xor_comm _ _
      _ = 0 := hzero
  have hcond : (UInt256.xor (PatternedWordData.expectedWordAt 5)
      (MachineState.readWord input 160)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 17775265432785288859418840296405106407947132191047579206632289663109943557538)
        (MachineState.readWord input 160)).toNat = 0 := by
    have hconst :
        (UInt256.ofNat 17775265432785288859418840296405106407947132191047579206632289663109943557538 : UInt256) =
          (17775265432785288859418840296405106407947132191047579206632289663109943557538 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_5] using hcond
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word5ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      word5Entry, word6Entry, frame, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
      BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.widePc4111,
      PrefixStatePaths.widePc4112,
      PrefixStatePaths.widePc4113,
      PrefixStatePaths.widePc4114,
      PrefixStatePaths.widePc4115,
      PrefixStatePaths.widePc4116,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-2 guard on a mismatch: the `JUMPI` is taken. -/
theorem run_word5Compare_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 160 ≠
      PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.word5ComparePath
      (word5Entry s input) = some (hit1Entry s input) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 5)
      (MachineState.readWord input 160)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 5)
        (MachineState.readWord input 160) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 160)
      (PatternedWordData.expectedWordAt 5)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 5)
      (MachineState.readWord input 160)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 5)
        (MachineState.readWord input 160) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 17775265432785288859418840296405106407947132191047579206632289663109943557538)
        (MachineState.readWord input 160)).toNat ≠ 0 := by
    have hconst :
        (UInt256.ofNat 17775265432785288859418840296405106407947132191047579206632289663109943557538 : UInt256) =
          (17775265432785288859418840296405106407947132191047579206632289663109943557538 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_5] using hcond'
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word5ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      word5Entry, hit1Entry, frame, hcalldata, hcode, hrun,
      htrue, htrue', hcond, hcond', hcondLit, BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.widePc4111,
      PrefixStatePaths.widePc4112,
      PrefixStatePaths.widePc4113,
      PrefixStatePaths.widePc4114,
      PrefixStatePaths.widePc4115,
      PrefixStatePaths.widePc4116,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]


theorem run_word6Compare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 192 =
      PatternedWordData.expectedWordAt 6)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.word6ComparePath
      (word6Entry s input) = some (word7Entry s input) := by
  have hzero : UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 6)
      (MachineState.readWord input 192) = 0 := by
    calc
      UInt256.xor (PatternedWordData.expectedWordAt 6)
          (MachineState.readWord input 192) =
        UInt256.xor (MachineState.readWord input 192)
          (PatternedWordData.expectedWordAt 6) := BooleanSelect.xor_comm _ _
      _ = 0 := hzero
  have hcond : (UInt256.xor (PatternedWordData.expectedWordAt 6)
      (MachineState.readWord input 192)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 90427351570519066560079137287317450753818552617089646512985429813514949107010)
        (MachineState.readWord input 192)).toNat = 0 := by
    have hconst :
        (UInt256.ofNat 90427351570519066560079137287317450753818552617089646512985429813514949107010 : UInt256) =
          (90427351570519066560079137287317450753818552617089646512985429813514949107010 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_6] using hcond
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word6ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      word6Entry, word7Entry, frame, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
      BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.widePc4117,
      PrefixStatePaths.widePc4118,
      PrefixStatePaths.widePc4119,
      PrefixStatePaths.widePc4120,
      PrefixStatePaths.widePc4121,
      PrefixStatePaths.widePc4122,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-2 guard on a mismatch: the `JUMPI` is taken. -/
theorem run_word6Compare_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 192 ≠
      PatternedWordData.expectedWordAt 6)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.word6ComparePath
      (word6Entry s input) = some (hit1Entry s input) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 6)
      (MachineState.readWord input 192)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 6)
        (MachineState.readWord input 192) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 192)
      (PatternedWordData.expectedWordAt 6)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 6)
      (MachineState.readWord input 192)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 6)
        (MachineState.readWord input 192) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 90427351570519066560079137287317450753818552617089646512985429813514949107010)
        (MachineState.readWord input 192)).toNat ≠ 0 := by
    have hconst :
        (UInt256.ofNat 90427351570519066560079137287317450753818552617089646512985429813514949107010 : UInt256) =
          (90427351570519066560079137287317450753818552617089646512985429813514949107010 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_6] using hcond'
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word6ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      word6Entry, hit1Entry, frame, hcalldata, hcode, hrun,
      htrue, htrue', hcond, hcond', hcondLit, BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.widePc4117,
      PrefixStatePaths.widePc4118,
      PrefixStatePaths.widePc4119,
      PrefixStatePaths.widePc4120,
      PrefixStatePaths.widePc4121,
      PrefixStatePaths.widePc4122,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]


theorem run_word7Compare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 224 =
      PatternedWordData.expectedWordAt 7)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.word7ComparePath
      (word7Entry s input) = some (hit2Entry s input) := by
  have hzero : UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hword
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 7)
      (MachineState.readWord input 224) = 0 := by
    calc
      UInt256.xor (PatternedWordData.expectedWordAt 7)
          (MachineState.readWord input 224) =
        UInt256.xor (MachineState.readWord input 224)
          (PatternedWordData.expectedWordAt 7) := BooleanSelect.xor_comm _ _
      _ = 0 := hzero
  have hcond : (UInt256.xor (PatternedWordData.expectedWordAt 7)
      (MachineState.readWord input 224)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 46836809398124041301509275424151671459047373308733951134252891636799006558445)
        (MachineState.readWord input 224)).toNat = 0 := by
    have hconst :
        (UInt256.ofNat 46836809398124041301509275424151671459047373308733951134252891636799006558445 : UInt256) =
          (46836809398124041301509275424151671459047373308733951134252891636799006558445 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_7] using hcond
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word7ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      word7Entry, hit2Entry, frame, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
      BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.widePc4123,
      PrefixStatePaths.widePc4124,
      PrefixStatePaths.widePc4125,
      PrefixStatePaths.widePc4126,
      PrefixStatePaths.widePc4127,
      PrefixStatePaths.widePc4128,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-2 guard on a mismatch: the `JUMPI` is taken. -/
theorem run_word7Compare_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 224 ≠
      PatternedWordData.expectedWordAt 7)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.word7ComparePath
      (word7Entry s input) = some (hit1Entry s input) := by
  have htrue : UInt256.isTrue (UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7)) := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 7)
      (MachineState.readWord input 224)) := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 7)
        (MachineState.readWord input 224) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcond : (UInt256.xor (MachineState.readWord input 224)
      (PatternedWordData.expectedWordAt 7)).toNat ≠ 0 := by
    intro hz
    apply hword
    apply (KnownInputLogic.wordXor_eq_zero_iff _ _).1
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 7)
      (MachineState.readWord input 224)).toNat ≠ 0 := by
    intro hz
    apply hword
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 7)
        (MachineState.readWord input 224) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondLit :
      (UInt256.xor
        (UInt256.ofNat 46836809398124041301509275424151671459047373308733951134252891636799006558445)
        (MachineState.readWord input 224)).toNat ≠ 0 := by
    have hconst :
        (UInt256.ofNat 46836809398124041301509275424151671459047373308733951134252891636799006558445 : UInt256) =
          (46836809398124041301509275424151671459047373308733951134252891636799006558445 : UInt256) := by
      rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_7] using hcond'
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.word7ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      word7Entry, hit1Entry, frame, hcalldata, hcode, hrun,
      htrue, htrue', hcond, hcond', hcondLit, BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.widePc4123,
      PrefixStatePaths.widePc4124,
      PrefixStatePaths.widePc4125,
      PrefixStatePaths.widePc4126,
      PrefixStatePaths.widePc4127,
      PrefixStatePaths.widePc4128,
      jumpDest_hit1,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]


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

/-- Execute the word-1 guard, the depth-4 rung and the matching install. -/
def gasSteps_finish (s : State) (input : ByteArray)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry s input)
      (if MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1 then
        (if PrefixStateModel.Matched2 input then PrefixStateMemory.resultState2 s input
          else PrefixStateMemory.resultState s input 0)
      else DriverTrace.compressEntry s input 0) := by
  have ghit1 : Challenge.EvmProof.GasSteps (hit1Entry s input)
      (PrefixStateMemory.resultState s input 0) :=
    frameBlock PrefixStatePaths.hitPath s input 5333 _ hcode hfork hrun hnp
      (run_hit1 s input hcode hrun)
  have ghit2 : Challenge.EvmProof.GasSteps (hit2Entry s input)
      (PrefixStateMemory.resultState2 s input) :=
    frameBlock PrefixStatePaths.hit2Path s input 5286 _ hcode hfork hrun hnp
      (run_hit2 s input hcode hrun)
  by_cases hw1 : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1
  · rw [if_pos hw1]
    have gsecond : Challenge.EvmProof.GasSteps (entry s input) (rungEntry s input) :=
      frameBlock PrefixStatePaths.secondComparePath s input 4999 _ hcode hfork hrun hnp
        (run_secondCompare_hit s input hw1 hcalldata hcode hrun)
    by_cases hw2 : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2
    · have g2 : Challenge.EvmProof.GasSteps (rungEntry s input) (fourthEntry s input) :=
        frameBlock PrefixStatePaths.thirdComparePath s input 5040 _ hcode hfork hrun hnp
          (run_thirdCompare_hit s input hw2 hcalldata hcode hrun)
      by_cases hw3 : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3
      · have g3 : Challenge.EvmProof.GasSteps (fourthEntry s input) (word4Entry s input) :=
          frameBlock PrefixStatePaths.fourthComparePath s input 5081 _ hcode hfork hrun hnp
            (run_fourthCompare_hit s input hw3 hcalldata hcode hrun)
        by_cases hw4 : MachineState.readWord input 128 = PatternedWordData.expectedWordAt 4
        · have g4 : Challenge.EvmProof.GasSteps (word4Entry s input) (word5Entry s input) :=
            frameBlock PrefixStatePaths.word4ComparePath s input 5122 _ hcode hfork hrun hnp
              (run_word4Compare_hit s input hw4 hcalldata hcode hrun)
          by_cases hw5 : MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5
          · have g5 : Challenge.EvmProof.GasSteps (word5Entry s input) (word6Entry s input) :=
              frameBlock PrefixStatePaths.word5ComparePath s input 5163 _ hcode hfork hrun hnp
                (run_word5Compare_hit s input hw5 hcalldata hcode hrun)
            by_cases hw6 : MachineState.readWord input 192 = PatternedWordData.expectedWordAt 6
            · have g6 : Challenge.EvmProof.GasSteps (word6Entry s input) (word7Entry s input) :=
                frameBlock PrefixStatePaths.word6ComparePath s input 5204 _ hcode hfork hrun hnp
                  (run_word6Compare_hit s input hw6 hcalldata hcode hrun)
              by_cases hw7 : MachineState.readWord input 224 = PatternedWordData.expectedWordAt 7
              · have g7 : Challenge.EvmProof.GasSteps (word7Entry s input) (hit2Entry s input) :=
                  frameBlock PrefixStatePaths.word7ComparePath s input 5245 _ hcode hfork hrun hnp
                    (run_word7Compare_hit s input hw7 hcalldata hcode hrun)
                rw [if_pos ⟨hw2, hw3, hw4, hw5, hw6, hw7⟩]
                exact gsecond.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (ghit2)))))))
              · rw [if_neg (fun h => hw7 h.2.2.2.2.2)]
                have gm : Challenge.EvmProof.GasSteps (word7Entry s input) (hit1Entry s input) :=
                  frameBlock PrefixStatePaths.word7ComparePath s input 5245 _ hcode hfork hrun hnp
                    (run_word7Compare_miss s input hw7 hcalldata hcode hrun)
                exact gsecond.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (gm.trans (ghit1)))))))
            · rw [if_neg (fun h => hw6 h.2.2.2.2.1)]
              have gm : Challenge.EvmProof.GasSteps (word6Entry s input) (hit1Entry s input) :=
                frameBlock PrefixStatePaths.word6ComparePath s input 5204 _ hcode hfork hrun hnp
                  (run_word6Compare_miss s input hw6 hcalldata hcode hrun)
              exact gsecond.trans (g2.trans (g3.trans (g4.trans (g5.trans (gm.trans (ghit1))))))
          · rw [if_neg (fun h => hw5 h.2.2.2.1)]
            have gm : Challenge.EvmProof.GasSteps (word5Entry s input) (hit1Entry s input) :=
              frameBlock PrefixStatePaths.word5ComparePath s input 5163 _ hcode hfork hrun hnp
                (run_word5Compare_miss s input hw5 hcalldata hcode hrun)
            exact gsecond.trans (g2.trans (g3.trans (g4.trans (gm.trans (ghit1)))))
        · rw [if_neg (fun h => hw4 h.2.2.1)]
          have gm : Challenge.EvmProof.GasSteps (word4Entry s input) (hit1Entry s input) :=
            frameBlock PrefixStatePaths.word4ComparePath s input 5122 _ hcode hfork hrun hnp
              (run_word4Compare_miss s input hw4 hcalldata hcode hrun)
          exact gsecond.trans (g2.trans (g3.trans (gm.trans (ghit1))))
      · rw [if_neg (fun h => hw3 h.2.1)]
        have gm : Challenge.EvmProof.GasSteps (fourthEntry s input) (hit1Entry s input) :=
          frameBlock PrefixStatePaths.fourthComparePath s input 5081 _ hcode hfork hrun hnp
            (run_fourthCompare_miss s input hw3 hcalldata hcode hrun)
        exact gsecond.trans (g2.trans (gm.trans (ghit1)))
    · rw [if_neg (fun h => hw2 h.1)]
      have gm : Challenge.EvmProof.GasSteps (rungEntry s input) (hit1Entry s input) :=
        frameBlock PrefixStatePaths.thirdComparePath s input 5040 _ hcode hfork hrun hnp
          (run_thirdCompare_miss s input hw2 hcalldata hcode hrun)
      exact gsecond.trans (gm.trans (ghit1))
  · rw [if_neg hw1]
    exact frameBlock PrefixStatePaths.secondComparePath s input 4999 _ hcode hfork hrun hnp
      (run_secondCompare_miss s input hw1 hcalldata hcode hrun)

#print axioms run_hit1
#print axioms run_hit2
#print axioms run_secondCompare_hit
#print axioms run_secondCompare_miss
#print axioms run_thirdCompare_hit
#print axioms run_thirdCompare_miss
#print axioms run_fourthCompare_hit
#print axioms run_fourthCompare_miss
#print axioms gasSteps_finish

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish
