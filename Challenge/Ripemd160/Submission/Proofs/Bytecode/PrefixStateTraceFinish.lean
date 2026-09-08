import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStatePaths
import Challenge.Ripemd160.Submission.Proofs.Bytecode.BooleanSelect

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- Entry at the second word comparison in the checked H8 prefix. -/
def entry (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 5219
    stack := [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

/-- Entry at the H1 stores after the second word guard has matched. -/
def hitEntry (s : State) (input : ByteArray) : State :=
  { s with
    pc := UInt256.ofNat 5260
    stack := [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

/-- The generic compression target of the guard is a valid jump destination. -/
theorem jumpDest_generic : Decode.isValidJumpDest submissionBytecode 464 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 272 = 464 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 272 (by rfl)
  rw [hpc] at h
  exact h

/-- The H1 stores return to the driver's `102` continuation. -/
theorem run_hit (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.hitPath
      (hitEntry s input) =
      some (PrefixStateMemory.resultState s input 0) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 102 = true := by
    have hpc : Artifact.submissionArtifact.instructionPC 64 = 102 := by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]
      decide
    have h := Artifact.submissionArtifact.isValidJumpDest_index 64 (by rfl)
    rw [hpc] at h
    exact h
  simp (config := { maxSteps := 500000 })
    [PrefixStatePaths.hitPath,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      hitEntry, PrefixStateMemory.resultState,
      PrefixStateMemory.hashMemory, PrefixStateMemory.writeWord,
      PrefixStateMemory.hash, FastEmptyBlock.emptyActiveWords,
      hcode, hrun, hdest,
      PrefixStatePaths.pc4034, PrefixStatePaths.pc4035,
      PrefixStatePaths.pc4036, PrefixStatePaths.pc4037,
      PrefixStatePaths.pc4038, PrefixStatePaths.pc4039,
      PrefixStatePaths.pc4040, PrefixStatePaths.pc4041,
      PrefixStatePaths.pc4042, PrefixStatePaths.pc4043,
      PrefixStatePaths.pc4044, PrefixStatePaths.pc4045,
      PrefixStatePaths.pc4046, PrefixStatePaths.pc4047,
      PrefixStatePaths.pc4048, PrefixStatePaths.pc4049,
      PrefixStatePaths.pc4050,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- The second word guard falls through to the H1 stores on a match. -/
theorem run_secondCompare_hit (s : State) (input : ByteArray)
    (hword : MachineState.readWord input 32 =
      PatternedWordData.expectedWordAt 1)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock PrefixStatePaths.secondComparePath
      (entry s input) = some (hitEntry s input) := by
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
      entry, hitEntry, hcalldata, hrun, hzero, hzero', hcond, hcondLit,
      BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4028, PrefixStatePaths.pc4029,
      PrefixStatePaths.pc4030, PrefixStatePaths.pc4031,
      PrefixStatePaths.pc4032, PrefixStatePaths.pc4033,
      jumpDest_generic,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- The second word guard jumps to the generic compressor on a mismatch. -/
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
      entry, DriverTrace.compressEntry, hcalldata, hcode, hrun,
      htrue, htrue', hcond, hcond', hcondLit, BooleanSelect.xor_comm, UInt256.isTrue,
      PrefixStatePaths.pc4028, PrefixStatePaths.pc4029,
      PrefixStatePaths.pc4030, PrefixStatePaths.pc4031,
      PrefixStatePaths.pc4032, PrefixStatePaths.pc4033,
      jumpDest_generic,
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

/-- Execute the second word guard and, on a match, the H1 store/return block. -/
def gasSteps_finish (s : State) (input : ByteArray)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (entry s input)
      (if MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1 then
        PrefixStateMemory.resultState s input 0
      else DriverTrace.compressEntry s input 0) := by
  by_cases hword : MachineState.readWord input 32 = PatternedWordData.expectedWordAt 1
  · rw [if_pos hword]
    have gsecond : Challenge.EvmProof.GasSteps (entry s input) (hitEntry s input) :=
      gasStepsBlock PrefixStatePaths.secondComparePath (entry s input) (hitEntry s input)
        (by simpa [entry] using hcode)
        (by simpa [entry, State.fork] using hfork)
        (run_secondCompare_hit s input hword hcalldata hcode hrun)
        (by simpa [entry] using hrun)
        (by simpa [entry] using hnp)
    have ghit : Challenge.EvmProof.GasSteps (hitEntry s input)
        (PrefixStateMemory.resultState s input 0) :=
      gasStepsBlock PrefixStatePaths.hitPath (hitEntry s input)
        (PrefixStateMemory.resultState s input 0)
        (by simpa [hitEntry] using hcode)
        (by simpa [hitEntry, State.fork] using hfork)
        (run_hit s input hcode hrun)
        (by simpa [hitEntry] using hrun)
        (by simpa [hitEntry] using hnp)
    exact gsecond.trans ghit
  · rw [if_neg hword]
    exact gasStepsBlock PrefixStatePaths.secondComparePath (entry s input)
      (DriverTrace.compressEntry s input 0)
      (by simpa [entry] using hcode)
      (by simpa [entry, State.fork] using hfork)
      (run_secondCompare_miss s input hword hcalldata hcode hrun)
      (by simpa [entry] using hrun)
      (by simpa [entry] using hnp)

#print axioms run_hit
#print axioms run_secondCompare_hit
#print axioms run_secondCompare_miss
#print axioms gasSteps_finish

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFinish
