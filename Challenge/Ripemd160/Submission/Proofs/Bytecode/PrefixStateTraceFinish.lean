import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

/-!
# Checked-prefix finish: word-1 guard, the depth-2 ladder rung, and the installs

After the word-0 match the dispatcher checks calldata word 1.  On a match it
falls into the depth-2 rung, which checks words 2 and 3: if both match it
installs `H2` and returns to the driver with block 1 consumed
(`resultState2`); otherwise it jumps to the depth-1 install of `H1`
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
def entry (s : State) (input : ByteArray) : State := frame s input 5012

/-- Entry at the depth-2 rung (word-2 comparison). -/
def rungEntry (s : State) (input : ByteArray) : State := frame s input 5053

/-- Entry at the word-3 comparison. -/
def fourthEntry (s : State) (input : ByteArray) : State := frame s input 5094

/-- Entry at the depth-3 word-4 comparison. -/
def fifthEntry (s : State) (input : ByteArray) : State := frame s input 5135

/-- Entry at the `H2` install after the depth-3 guard misses. -/
def hit2Entry (s : State) (input : ByteArray) : State := frame s input 5182

/-- Entry at the `H1` install (`JUMPDEST` target of the rung's guards). -/
def hit1Entry (s : State) (input : ByteArray) : State := frame s input 5229

/-- Entry at the `H3` word-5 comparison. -/
def h3CompareEntry (s : State) (input : ByteArray) : State := frame s input 5272

/-- Entry at the `H3` install after both depth-3 words matched. -/
def h3InstallEntry (s : State) (input : ByteArray) : State := frame s input 5314

/-- The generic compression target of the guard is a valid jump destination. -/
theorem jumpDest_generic : Decode.isValidJumpDest submissionBytecode 464 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 272 = 464 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 272 (by rfl)
  rw [hpc] at h
  exact h

/-- The `H2` install entry is a valid jump destination. -/
theorem jumpDest_hit2 : Decode.isValidJumpDest submissionBytecode 5182 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4117 = 5182 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4117 (by rfl)
  rw [hpc] at h
  exact h

/-- The `H1` install entry is a valid jump destination. -/
theorem jumpDest_hit1 : Decode.isValidJumpDest submissionBytecode 5229 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4138 = 5229 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4138 (by rfl)
  rw [hpc] at h
  exact h

/-- The `H3` comparison entry is a valid jump destination. -/
theorem jumpDest_h3Compare : Decode.isValidJumpDest submissionBytecode 5272 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 4156 = 5272 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 4156 (by rfl)
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
      PrefixStatePaths.pc4138,
      PrefixStatePaths.pc4139,
      PrefixStatePaths.pc4140,
      PrefixStatePaths.pc4141,
      PrefixStatePaths.pc4142,
      PrefixStatePaths.pc4143,
      PrefixStatePaths.pc4144,
      PrefixStatePaths.pc4145,
      PrefixStatePaths.pc4146,
      PrefixStatePaths.pc4147,
      PrefixStatePaths.pc4148,
      PrefixStatePaths.pc4149,
      PrefixStatePaths.pc4150,
      PrefixStatePaths.pc4151,
      PrefixStatePaths.pc4152,
      PrefixStatePaths.pc4153,
      PrefixStatePaths.pc4154,
      PrefixStatePaths.pc4155,
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
  have hbo : DriverTrace.blockOffsetWord 1 = UInt256.ofNat 64 := rfl
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hit2Path,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hit2Entry, frame, PrefixStateMemory.resultState2,
      PrefixStateMemory.hashMemory2, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash2, FastEmptyBlock.emptyActiveWords,
      hcode, hrun, jumpDest_driver, hbo, List.exchange,
      PrefixStatePaths.pc4117,
      PrefixStatePaths.pc4118,
      PrefixStatePaths.pc4119,
      PrefixStatePaths.pc4120,
      PrefixStatePaths.pc4121,
      PrefixStatePaths.pc4122,
      PrefixStatePaths.pc4123,
      PrefixStatePaths.pc4124,
      PrefixStatePaths.pc4125,
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
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- Word-4 guard on a match: the `EQ` jump enters the H3 word-5 check. -/
theorem run_fifthCompare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 128 =
      PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.fifthComparePath
      (fifthEntry s input) = some (h3CompareEntry s input) := by
  have hword' : MachineState.readWord input 128 = UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146 := by
    simpa only [PatternedWordData.expectedWordAt_4] using hword
  have heq : UInt256.eq (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146)
      (MachineState.readWord input 128) = UInt256.ofNat 1 := by
    rw [hword']
    decide
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.fifthComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      fifthEntry, h3CompareEntry, frame, hcalldata, hrun, heq,
      UInt256.isTrue, UInt256.eq,
      PrefixStatePaths.pc4105,
      PrefixStatePaths.pc4106,
      PrefixStatePaths.pc4107,
      PrefixStatePaths.pc4108,
      PrefixStatePaths.pc4109,
      PrefixStatePaths.pc4110,
      jumpDest_h3Compare,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-4 guard on a mismatch: the padding destinations fall through to H2. -/
theorem run_fifthCompare_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 128 ≠
      PatternedWordData.expectedWordAt 4)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.fifthCompareMissPath
      (fifthEntry s input) = some (hit2Entry s input) := by
  have hne : (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146) ≠ MachineState.readWord input 128 := by
    intro h
    apply hword
    simpa only [PatternedWordData.expectedWordAt_4] using h.symm
  have hneNat : (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146).toNat ≠
      (MachineState.readWord input 128).toNat := by
    intro hz
    apply hne
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have heq : UInt256.eq (UInt256.ofNat 61367581353886127001238131413293229573374005415347599533452268822761471270146)
      (MachineState.readWord input 128) = UInt256.ofNat 0 := by
    rw [UInt256.eq, Exp.toNat_ofNat_self (by norm_num), if_neg hneNat]
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.fifthCompareMissPath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      fifthEntry, hit2Entry, frame, hcalldata, hcode, hrun, heq,
      UInt256.isTrue, UInt256.eq,
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
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-5 guard on a match: the XOR jump falls through to the H3 stores. -/
theorem run_h3Compare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 160 =
      PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.h3ComparePath
      (h3CompareEntry s input) = some (h3InstallEntry s input) := by
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
          (17775265432785288859418840296405106407947132191047579206632289663109943557538 : UInt256) := by rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_5] using hcond
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.h3ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      h3CompareEntry, h3InstallEntry, frame, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
      BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4156,
      PrefixStatePaths.pc4157,
      PrefixStatePaths.pc4158,
      PrefixStatePaths.pc4159,
      PrefixStatePaths.pc4160,
      PrefixStatePaths.pc4161,
      PrefixStatePaths.pc4162,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Word-5 guard on a mismatch: the XOR jump returns to H2. -/
theorem run_h3Compare_miss (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 160 ≠
      PatternedWordData.expectedWordAt 5)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.h3ComparePath
      (h3CompareEntry s input) = some (hit2Entry s input) := by
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
          (17775265432785288859418840296405106407947132191047579206632289663109943557538 : UInt256) := by rfl
    rw [hconst]
    simpa only [PatternedWordData.expectedWordAt_5] using hcond'
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.h3ComparePath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      h3CompareEntry, hit2Entry, frame, hcalldata, hcode, hrun,
      htrue, htrue', hcond, hcond', hcondLit, BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4156,
      PrefixStatePaths.pc4157,
      PrefixStatePaths.pc4158,
      PrefixStatePaths.pc4159,
      PrefixStatePaths.pc4160,
      PrefixStatePaths.pc4161,
      PrefixStatePaths.pc4162,
      jumpDest_hit2,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- Store `H3` and return to the driver's block-2 continuation. -/
theorem run_h3Install (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.h3InstallPath
      (h3InstallEntry s input) =
      some (PrefixStateMemory.resultState3 s input) := by
  have hbo : DriverTrace.blockOffsetWord 2 = UInt256.ofNat 128 := rfl
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.h3InstallPath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      h3InstallEntry, frame, PrefixStateMemory.resultState3,
      PrefixStateMemory.hashMemory3, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash3, FastEmptyBlock.emptyActiveWords,
      hcode, hrun, jumpDest_driver, hbo, List.exchange,
      PrefixStatePaths.pc4163,
      PrefixStatePaths.pc4164,
      PrefixStatePaths.pc4165,
      PrefixStatePaths.pc4166,
      PrefixStatePaths.pc4167,
      PrefixStatePaths.pc4168,
      PrefixStatePaths.pc4169,
      PrefixStatePaths.pc4170,
      PrefixStatePaths.pc4171,
      PrefixStatePaths.pc4172,
      PrefixStatePaths.pc4173,
      PrefixStatePaths.pc4174,
      PrefixStatePaths.pc4175,
      PrefixStatePaths.pc4176,
      PrefixStatePaths.pc4177,
      PrefixStatePaths.pc4178,
      PrefixStatePaths.pc4179,
      PrefixStatePaths.pc4180,
      PrefixStatePaths.pc4181,
      PrefixStatePaths.pc4182,
      PrefixStatePaths.pc4183,
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
      (fourthEntry s input) = some (hit2Entry s input) := by
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
      fourthEntry, hit2Entry, frame, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
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

/-- Execute the word-1 guard, the depth-2 rung and the matching install. -/
def gasSteps_finish (s : State) (input : ByteArray)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry s input)
      (if MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1 then
        (if PrefixStateModel.Matched2 input then
          (if PrefixStateModel.Matched3 input then PrefixStateMemory.resultState3 s input
            else PrefixStateMemory.resultState2 s input)
          else PrefixStateMemory.resultState s input 0)
      else DriverTrace.compressEntry s input 0) := by
  have ghit1 : Challenge.EvmProof.GasSteps (hit1Entry s input)
      (PrefixStateMemory.resultState s input 0) :=
    frameBlock PrefixStatePaths.hitPath s input 5229 _ hcode hfork hrun hnp
      (run_hit1 s input hcode hrun)
  have ghit2 : Challenge.EvmProof.GasSteps (hit2Entry s input)
      (PrefixStateMemory.resultState2 s input) :=
    frameBlock PrefixStatePaths.hit2Path s input 5182 _ hcode hfork hrun hnp
      (run_hit2 s input hcode hrun)
  have ghit3 : Challenge.EvmProof.GasSteps (h3InstallEntry s input)
      (PrefixStateMemory.resultState3 s input) :=
    frameBlock PrefixStatePaths.h3InstallPath s input 5314 _ hcode hfork hrun hnp
      (run_h3Install s input hcode hrun)
  by_cases hw1 : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1
  · rw [if_pos hw1]
    have gsecond : Challenge.EvmProof.GasSteps (entry s input) (rungEntry s input) :=
      frameBlock PrefixStatePaths.secondComparePath s input 5012 _ hcode hfork hrun hnp
        (run_secondCompare_hit s input hw1 hcalldata hcode hrun)
    by_cases hw2 : MachineState.readWord input 64 = PatternedWordData.expectedWordAt 2
    · have gthird : Challenge.EvmProof.GasSteps (rungEntry s input) (fourthEntry s input) :=
        frameBlock PrefixStatePaths.thirdComparePath s input 5053 _ hcode hfork hrun hnp
          (run_thirdCompare_hit s input hw2 hcalldata hcode hrun)
      by_cases hw3 : MachineState.readWord input 96 = PatternedWordData.expectedWordAt 3
      · rw [if_pos ⟨hw2, hw3⟩]
        have gfourth : Challenge.EvmProof.GasSteps (fourthEntry s input) (fifthEntry s input) :=
          frameBlock PrefixStatePaths.fourthComparePath s input 5094 _ hcode hfork hrun hnp
            (run_fourthCompare_hit s input hw3 hcalldata hcode hrun)
        by_cases hw4 : MachineState.readWord input 128 = PatternedWordData.expectedWordAt 4
        · have gfifth : Challenge.EvmProof.GasSteps (fifthEntry s input) (h3CompareEntry s input) :=
            frameBlock PrefixStatePaths.fifthComparePath s input 5135 _ hcode hfork hrun hnp
              (run_fifthCompare_hit s input hw4 hcalldata hcode hrun)
          by_cases hw5 : MachineState.readWord input 160 = PatternedWordData.expectedWordAt 5
          · rw [if_pos ⟨hw4, hw5⟩]
            have gh3 : Challenge.EvmProof.GasSteps (h3CompareEntry s input) (h3InstallEntry s input) :=
              frameBlock PrefixStatePaths.h3ComparePath s input 5272 _ hcode hfork hrun hnp
                (run_h3Compare_hit s input hw5 hcalldata hcode hrun)
            exact gsecond.trans (gthird.trans (gfourth.trans (gfifth.trans (gh3.trans ghit3))))
          · rw [if_neg (fun h => hw5 h.2)]
            have gh3 : Challenge.EvmProof.GasSteps (h3CompareEntry s input) (hit2Entry s input) :=
              frameBlock PrefixStatePaths.h3ComparePath s input 5272 _ hcode hfork hrun hnp
                (run_h3Compare_miss s input hw5 hcalldata hcode hrun)
            exact gsecond.trans (gthird.trans (gfourth.trans (gfifth.trans (gh3.trans ghit2))))
        · rw [if_neg (fun h => hw4 h.1)]
          have gfifth : Challenge.EvmProof.GasSteps (fifthEntry s input) (hit2Entry s input) :=
            frameBlock PrefixStatePaths.fifthCompareMissPath s input 5135 _ hcode hfork hrun hnp
              (run_fifthCompare_miss s input hw4 hcalldata hcode hrun)
          exact gsecond.trans (gthird.trans (gfourth.trans (gfifth.trans ghit2)))
      · rw [if_neg (fun h => hw3 h.2)]
        have gfourth : Challenge.EvmProof.GasSteps (fourthEntry s input) (hit1Entry s input) :=
          frameBlock PrefixStatePaths.fourthComparePath s input 5094 _ hcode hfork hrun hnp
            (run_fourthCompare_miss s input hw3 hcalldata hcode hrun)
        exact gsecond.trans (gthird.trans (gfourth.trans ghit1))
    · rw [if_neg (fun h => hw2 h.1)]
      have gthird : Challenge.EvmProof.GasSteps (rungEntry s input) (hit1Entry s input) :=
        frameBlock PrefixStatePaths.thirdComparePath s input 5053 _ hcode hfork hrun hnp
          (run_thirdCompare_miss s input hw2 hcalldata hcode hrun)
      exact gsecond.trans (gthird.trans ghit1)
  · rw [if_neg hw1]
    exact frameBlock PrefixStatePaths.secondComparePath s input 5012 _ hcode hfork hrun hnp
      (run_secondCompare_miss s input hw1 hcalldata hcode hrun)

#print axioms run_hit1
#print axioms run_hit2
#print axioms run_secondCompare_hit
#print axioms run_secondCompare_miss
#print axioms run_thirdCompare_hit
#print axioms run_thirdCompare_miss
#print axioms run_fourthCompare_hit
#print axioms run_fourthCompare_miss
#print axioms run_fifthCompare_hit
#print axioms run_fifthCompare_miss
#print axioms run_h3Compare_hit
#print axioms run_h3Compare_miss
#print axioms run_h3Install
#print axioms gasSteps_finish

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish
