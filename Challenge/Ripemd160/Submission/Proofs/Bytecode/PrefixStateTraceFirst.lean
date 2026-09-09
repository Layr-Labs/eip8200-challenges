import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateCodecopy
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# H8 first-block execution (index 0)

Raw `prefixPath` (instructions 4072..4078) from the nonempty dispatcher
entry to `PrefixStateCodecopy.preCopyState`, the generic `CODECOPY` step,
then `firstComparePath` (4080..4086: scratch `MLOAD`, word-0
`CALLDATALOAD`, `XOR`, `JUMPI`) ending at the compression entry on a word-0
mismatch and at `firstMatchedState` on a word-0 match.  Only the first block
(`i = 0`) is handled here.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFirst

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- Driver suffix preserved under the `CODECOPY` arguments: the concrete
four-element driver stack for block 0. -/
def rho (input : ByteArray) : List UInt256 :=
  [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
    DriverTrace.blockOffsetWord 0, Padding.paddedWord input]

@[simp] theorem rho_length (input : ByteArray) : (rho input).length = 4 := rfl

/-- State after the first comparison succeeds: pc 5012 (instruction 4087)
with the plain driver stack on top of the copied-code state. -/
def firstMatchedState (s : State) (input : ByteArray) : State :=
  { PrefixStateMemory.copied s with
    pc := UInt256.ofNat 5019
    stack := [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

/-- The same state with the scratch `MLOAD` active-words update still
explicit; it collapses by `PrefixStateMemory.scratchState_copied`. -/
private def firstMatchedScratch (s : State) (input : ByteArray) : State :=
  { PrefixStateMemory.scratchState (PrefixStateMemory.copied s) with
    pc := UInt256.ofNat 5019
    stack := [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

private theorem firstMatchedScratch_eq (s : State) (input : ByteArray) :
    firstMatchedScratch s input = firstMatchedState s input := by
  unfold firstMatchedScratch firstMatchedState
  rw [PrefixStateMemory.scratchState_copied]

theorem jumpDest_generic : Decode.isValidJumpDest submissionBytecode 464 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 272 = 464 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 272 (by rfl)
  rw [hpc] at h
  exact h

/-- The raw seven-instruction checked-prefix setup for block 0 ends exactly at
the generic `CODECOPY` pre-state. -/
theorem run_prefix (s : State) (input : ByteArray)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.prefixPath
      (FastEmptyBlock.nonemptyEntry s input 0) =
      some (PrefixStateCodecopy.preCopyState s (rho input)) := by
  have hdup : ((FastEmptyBlock.nonemptyEntry s input 0).stack[2]? :
      Option UInt256) = some (DriverTrace.blockOffsetWord 0) := by
    show ([DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
        DriverTrace.blockOffsetWord 0, Padding.paddedWord input][2]? :
      Option UInt256) = some _
    simp
  have hcond : ¬ UInt256.isTrue (DriverTrace.blockOffsetWord 0) := by
    show ¬ UInt256.isTrue (UInt256.ofNat 0)
    decide
  simp (config := { maxSteps := 1000000 })
    [PrefixStatePaths.prefixPath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, FastEmptyBlock.nonemptyEntry,
      PrefixStateCodecopy.preCopyState, rho, hdup, hcond,
      show DriverTrace.blockOffsetWord 0 = UInt256.ofNat 0 from rfl,
      PrefixStatePaths.pc4072, PrefixStatePaths.pc4073, PrefixStatePaths.pc4074,
      PrefixStatePaths.pc4075, PrefixStatePaths.pc4076, PrefixStatePaths.pc4077,
      PrefixStatePaths.pc4078,
      hrun, UInt256.isTrue, Nat.mod_eq_of_lt,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

private theorem zero_toNat : (⟨0⟩ : UInt256).toNat = 0 := rfl

private theorem cond_match (input : ByteArray)
    (hmatch : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0) :
    UInt256.isTrue
      (UInt256.xor (MachineState.readWord input 0) (PatternedWordData.expectedWordAt 0)) =
      false := by
  rw [hmatch]
  have hx : UInt256.xor (PatternedWordData.expectedWordAt 0)
      (PatternedWordData.expectedWordAt 0) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  unfold UInt256.isTrue
  rw [hx]
  decide

private theorem cond_mismatch (input : ByteArray)
    (hne : MachineState.readWord input 0 ≠ PatternedWordData.expectedWordAt 0) :
    UInt256.isTrue
      (UInt256.xor (MachineState.readWord input 0) (PatternedWordData.expectedWordAt 0)) =
      true := by
  have htrue : UInt256.isTrue
      (UInt256.xor (MachineState.readWord input 0) (PatternedWordData.expectedWordAt 0)) := by
    intro hzero
    apply hne
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).1
      (by apply Challenge.EvmProof.Word.word_ext; simpa using hzero)
  simpa using htrue

/-- The seven-instruction first-word comparison on a word-0 match: the final
`JUMPI` is not taken and execution continues at pc 5012 (instruction 4087). -/
theorem run_firstCompare_match (s : State) (input : ByteArray)
    (hmatch : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hcalldata : s.executionEnv.calldata = input)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.firstComparePath
      (PrefixStateCodecopy.copiedState s (rho input)) =
      some (firstMatchedState s input) := by
  have hword : MachineState.readWord (PrefixStateMemory.copied s).memory 0 =
      PatternedWordData.expectedWordAt 0 :=
    PrefixStateMemory.copied_word_zero s
  have hzero : UInt256.xor (MachineState.readWord input 0)
      (PatternedWordData.expectedWordAt 0) = 0 :=
    (KnownInputLogic.wordXor_eq_zero_iff _ _).2 hmatch
  have hzero' : UInt256.xor (PatternedWordData.expectedWordAt 0)
      (MachineState.readWord input 0) = 0 := by
    rw [hmatch]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  have hcond : (UInt256.xor (MachineState.readWord input 0)
      (PatternedWordData.expectedWordAt 0)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 0)
      (MachineState.readWord input 0)).toNat = 0 := by
    rw [hzero']
    rfl
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_0] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_0] at hcondL'
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor (MachineState.readWord input 0)
        (PatternedWordData.expectedWordAt 0)) := by
    rw [hzero]
    decide
  have hfalse' : ¬ UInt256.isTrue
      (UInt256.xor (PatternedWordData.expectedWordAt 0)
        (MachineState.readWord input 0)) := by
    rw [hzero']
    decide
  rw [← firstMatchedScratch_eq]
  simp (config := { maxSteps := 300000 })
    [PrefixStatePaths.firstComparePath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, PrefixStateCodecopy.copiedState, firstMatchedScratch,
      PrefixStateMemory.scratchState, rho,
      hword, hzero, hzero', hcond, hcond', hcondL, hcondL', hfalse, hfalse',
      cond_match input hmatch, zero_toNat,
      UInt256.isTrue, hrun, hcalldata, State.activeWordsAfterUInt256,
      PrefixStatePaths.pc4080, PrefixStatePaths.pc4081, PrefixStatePaths.pc4082,
      PrefixStatePaths.pc4083, PrefixStatePaths.pc4084, PrefixStatePaths.pc4085,
      PrefixStatePaths.pc4086,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- The seven-instruction first-word comparison on a word-0 mismatch: the
final `JUMPI` is taken to the generic compression entry at pc 464. -/
theorem run_firstCompare_mismatch (s : State) (input : ByteArray)
    (hne : MachineState.readWord input 0 ≠ PatternedWordData.expectedWordAt 0)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.firstComparePath
      (PrefixStateCodecopy.copiedState s (rho input)) =
      some (DriverTrace.compressEntry (PrefixStateMemory.copied s) input 0) := by
  have hword : MachineState.readWord (PrefixStateMemory.copied s).memory 0 =
      PatternedWordData.expectedWordAt 0 :=
    PrefixStateMemory.copied_word_zero s
  have hdest : Decode.isValidJumpDest submissionBytecode 464 = true := jumpDest_generic
  have htrue : UInt256.isTrue
      (UInt256.xor (MachineState.readWord input 0)
        (PatternedWordData.expectedWordAt 0)) = true :=
    cond_mismatch input hne
  have htrue' : UInt256.isTrue
      (UInt256.xor (PatternedWordData.expectedWordAt 0)
        (MachineState.readWord input 0)) = true := by
    have h : UInt256.isTrue (UInt256.xor (PatternedWordData.expectedWordAt 0)
        (MachineState.readWord input 0)) := by
      intro hz
      apply hne
      have hzero : UInt256.xor (PatternedWordData.expectedWordAt 0)
          (MachineState.readWord input 0) = 0 := by
        apply Challenge.EvmProof.Word.word_ext
        simpa using hz
      exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
    simpa using h
  have hcond : (UInt256.xor (MachineState.readWord input 0)
      (PatternedWordData.expectedWordAt 0)).toNat ≠ 0 := by
    intro hz
    apply hne
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).1
      (by apply Challenge.EvmProof.Word.word_ext; simpa using hz)
  have hcond' : (UInt256.xor (PatternedWordData.expectedWordAt 0)
      (MachineState.readWord input 0)).toNat ≠ 0 := by
    intro hz
    apply hne
    have hzero : UInt256.xor (PatternedWordData.expectedWordAt 0)
        (MachineState.readWord input 0) = 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simpa using hz
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1 hzero).symm
  have hcondL := hcond
  rw [PatternedWordData.expectedWordAt_0] at hcondL
  have hcondL' := hcond'
  rw [PatternedWordData.expectedWordAt_0] at hcondL'
  have hexit : DriverTrace.compressEntry (PrefixStateMemory.copied s) input 0 =
      DriverTrace.compressEntry
        (PrefixStateMemory.scratchState (PrefixStateMemory.copied s)) input 0 := by
    rw [PrefixStateMemory.scratchState_copied]
  rw [hexit]
  simp (config := { maxSteps := 300000 })
    [PrefixStatePaths.firstComparePath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, PrefixStateCodecopy.copiedState, DriverTrace.compressEntry,
      PrefixStateMemory.scratchState, rho,
      hword, htrue, htrue', hcond, hcond', hcondL, hcondL',
      cond_mismatch input hne, hdest, zero_toNat,
      UInt256.isTrue, hrun, hcode, hcalldata, State.activeWordsAfterUInt256,
      PrefixStatePaths.pc4080, PrefixStatePaths.pc4081, PrefixStatePaths.pc4082,
      PrefixStatePaths.pc4083, PrefixStatePaths.pc4084, PrefixStatePaths.pc4085,
      PrefixStatePaths.pc4086,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]

/-- The single generic `CODECOPY` step for block 0 through the provided
`PrefixStateCodecopy` lemma with the concrete four-word suffix. -/
def gasSteps_codecopy_first (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (PrefixStateCodecopy.preCopyState s (rho input))
      (PrefixStateCodecopy.copiedState s (rho input)) :=
  PrefixStateCodecopy.gasSteps_codecopy s (rho input) (by simp [rho]) hcode hrun hnp

/-- Combined first-block execution certificate: seven setup instructions, the
`CODECOPY` step, and seven comparison instructions, branching on the word-0
match.  Endpoints: `nonemptyEntry ... 0` to the branch target. -/
def gasSteps_first (s : State) (input : ByteArray)
    (hcalldata : s.executionEnv.calldata = input)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (FastEmptyBlock.nonemptyEntry s input 0)
      (if MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0 then
        firstMatchedState s input
        else DriverTrace.compressEntry (PrefixStateMemory.copied s) input 0) := by
  have gpre : GasSteps (FastEmptyBlock.nonemptyEntry s input 0)
      (PrefixStateCodecopy.preCopyState s (rho input)) := by
    exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
      PrefixStatePaths.prefixPath
      (by
        change s.executionEnv.code = submissionBytecode
        exact hcode)
      (by
        change s.fork = .Osaka
        exact hfork)
      (run_prefix s input hrun)
      (by
        change s.halt = .Running
        exact hrun)
      (by
        change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
          s.executionEnv.fork s.executionEnv.codeAddr = false
        exact hnp)
  have gcc := gasSteps_codecopy_first s input
    (by simpa [PrefixStateCodecopy.preCopyState] using hcode)
    (by simpa [PrefixStateCodecopy.preCopyState] using hrun)
    (by simpa [PrefixStateCodecopy.preCopyState] using hnp)
  by_cases hmatch : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0
  · have hrun' : (PrefixStateCodecopy.copiedState s (rho input)).halt = .Running := by
      simpa [PrefixStateCodecopy.copiedState, PrefixStateMemory.copied] using hrun
    have gcmp : GasSteps (PrefixStateCodecopy.copiedState s (rho input))
        (firstMatchedState s input) := by
      exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        PrefixStatePaths.firstComparePath
        (by
          change s.executionEnv.code = submissionBytecode
          exact hcode)
        (by
          change s.fork = .Osaka
          exact hfork)
        (run_firstCompare_match s input hmatch hcalldata hrun')
        hrun'
        (by
          change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
            s.executionEnv.fork s.executionEnv.codeAddr = false
          exact hnp)
    exact GasSteps.cast (gpre.trans (gcc.trans gcmp)) rfl (by rw [if_pos hmatch])
  · have hrun' : (PrefixStateCodecopy.copiedState s (rho input)).halt = .Running := by
      simpa [PrefixStateCodecopy.copiedState, PrefixStateMemory.copied] using hrun
    have gcmp : GasSteps (PrefixStateCodecopy.copiedState s (rho input))
        (DriverTrace.compressEntry (PrefixStateMemory.copied s) input 0) := by
      exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
        PrefixStatePaths.firstComparePath
        (by
          change s.executionEnv.code = submissionBytecode
          exact hcode)
        (by
          change s.fork = .Osaka
          exact hfork)
        (run_firstCompare_mismatch s input hmatch hcalldata hcode hrun')
        hrun'
        (by
          change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
            s.executionEnv.fork s.executionEnv.codeAddr = false
          exact hnp)
    exact GasSteps.cast (gpre.trans (gcc.trans gcmp)) rfl (by rw [if_neg hmatch])

#print axioms gasSteps_first

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFirst
