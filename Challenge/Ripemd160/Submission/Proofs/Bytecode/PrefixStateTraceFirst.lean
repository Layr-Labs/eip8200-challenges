import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateCodecopy
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-!
# H8 first-block execution (index 0)

Raw `prefixPath` (instructions 4287..4295) from the nonempty dispatcher
entry to `PrefixStateCodecopy.preCopyState`, the generic `CODECOPY` step,
then `firstComparePath` (4297..4301) ending at the compression entry on a
word-0 mismatch and at `firstMatchedState` on a word-0 match.  Only the
first block (`i = 0`) is handled here.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFirst

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- Driver suffix preserved under the `CODECOPY` arguments and the first
checked word: the concrete four-element driver stack for block 0 with the
`CALLDATALOAD` result on top. -/
def rho (input : ByteArray) : List UInt256 :=
  [MachineState.readWord input 0, DriverTrace.messageOffsetWord 0,
    UInt256.ofNat 102, DriverTrace.blockOffsetWord 0, Padding.paddedWord input]

@[simp] theorem rho_length (input : ByteArray) : (rho input).length = 5 := rfl

/-- State after the first comparison succeeds: pc 5224 (instruction 4302)
with the plain driver stack on top of the copied-code state. -/
def firstMatchedState (s : State) (input : ByteArray) : State :=
  { PrefixStateMemory.copied s with
    pc := UInt256.ofNat 5224
    stack := [DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
      DriverTrace.blockOffsetWord 0, Padding.paddedWord input] }

theorem jumpDest_generic : Decode.isValidJumpDest submissionBytecode 464 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 272 = 464 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 272 (by rfl)
  rw [hpc] at h
  exact h

/-- The raw nine-instruction checked-prefix setup for block 0 ends exactly at
the generic `CODECOPY` pre-state. -/
theorem run_prefix (s : State) (input : ByteArray)
    (hcalldata : s.executionEnv.calldata = input)
    (_hcode : s.executionEnv.code = submissionBytecode)
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
      PrefixStatePaths.pc4013, PrefixStatePaths.pc4014, PrefixStatePaths.pc4015,
      PrefixStatePaths.pc4016, PrefixStatePaths.pc4017, PrefixStatePaths.pc4018,
      PrefixStatePaths.pc4019, PrefixStatePaths.pc4020, PrefixStatePaths.pc4021,
      hcalldata, hrun, UInt256.isTrue, Nat.mod_eq_of_lt,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

/-- On the copied scratch state the `MLOAD` at offset 0 is already covered by
the high-water mark, so the active-words update is idempotent. -/
private theorem activeWordsAfterUInt256_idem (t : State)
    (hactive : 1 ≤ t.activeWords.toNat) :
    t.activeWordsAfterUInt256 0 32 = t.activeWords := by
  have hword : UInt256.ofNat t.activeWords.toNat = t.activeWords :=
    (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm
  have hcalc : MachineState.activeWordsAfter t.activeWords.toNat 0 32 =
      t.activeWords.toNat := by
    unfold MachineState.activeWordsAfter
    rw [if_neg (by norm_num : (32 : Nat) ≠ 0)]
    exact Nat.max_eq_left hactive
  unfold State.activeWordsAfterUInt256
  rw [hcalc, hword]

private theorem copied_active_ge (s : State) :
    1 ≤ (PrefixStateMemory.copied s).activeWords.toNat := by
  have ha : s.activeWords.toNat < 2 ^ 256 := s.activeWords.val.isLt
  have hmaxlt : Nat.max s.activeWords.toNat 1 < 2 ^ 256 := by
    exact (Nat.max_lt).2 ⟨ha, by norm_num⟩
  have hfirst : MachineState.activeWordsAfter s.activeWords.toNat 0 32 =
      Nat.max s.activeWords.toNat 1 := by
    unfold MachineState.activeWordsAfter
    rw [if_neg (by norm_num : (32 : Nat) ≠ 0)]
  change 1 ≤ (UInt256.ofNat
    (MachineState.activeWordsAfter s.activeWords.toNat 0 32)).toNat
  rw [hfirst, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hmaxlt]
  exact Nat.le_max_right _ _

private theorem act_idem (s : State) :
    (PrefixStateMemory.copied s).activeWordsAfterUInt256 0 32 =
      (PrefixStateMemory.copied s).activeWords :=
  activeWordsAfterUInt256_idem _ (copied_active_ge s)

private theorem compare_mload_active (s : State) (input : ByteArray) :
    ({ toSharedState := (PrefixStateMemory.copied s).toSharedState,
        pc := UInt256.ofNat 5218,
        stack := [UInt256.ofNat 0, MachineState.readWord input 0,
          DriverTrace.messageOffsetWord 0, UInt256.ofNat 102,
          DriverTrace.blockOffsetWord 0, Padding.paddedWord input],
        execLength := (PrefixStateMemory.copied s).execLength,
        halt := HaltKind.Running, callStack := s.callStack } : State).activeWordsAfterUInt256 0 32 =
      (PrefixStateMemory.copied s).activeWords := by
  change (PrefixStateMemory.copied s).activeWordsAfterUInt256 0 32 =
    (PrefixStateMemory.copied s).activeWords
  exact act_idem s

private theorem cond_match (input : ByteArray)
    (hmatch : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0) :
    UInt256.isTrue
      (UInt256.xor (PatternedWordData.expectedWordAt 0) (MachineState.readWord input 0)) =
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
      (UInt256.xor (PatternedWordData.expectedWordAt 0) (MachineState.readWord input 0)) =
      true := by
  have htrue : UInt256.isTrue
      (UInt256.xor (PatternedWordData.expectedWordAt 0) (MachineState.readWord input 0)) := by
    intro hzero
    apply hne
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1
      (by apply Challenge.EvmProof.Word.word_ext; simpa using hzero)).symm
  simpa using htrue

/-- The five-instruction first-word comparison on a word-0 match: the final
`JUMPI` is not taken and execution continues at pc 5224 (instruction 4302). -/
theorem run_firstCompare_match (s : State) (input : ByteArray)
    (hmatch : MachineState.readWord input 0 = PatternedWordData.expectedWordAt 0)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock PrefixStatePaths.firstComparePath
      (PrefixStateCodecopy.copiedState s (rho input)) =
      some (firstMatchedState s input) := by
  have hword : MachineState.readWord (PrefixStateMemory.copied s).memory 0 =
      PatternedWordData.expectedWordAt 0 :=
    PrefixStateMemory.copied_word_zero s
  have hzero : UInt256.xor (PatternedWordData.expectedWordAt 0)
      (MachineState.readWord input 0) = 0 := by
    rw [hmatch]
    exact (KnownInputLogic.wordXor_eq_zero_iff _ _).2 rfl
  have hcond : (UInt256.xor (PatternedWordData.expectedWordAt 0)
      (MachineState.readWord input 0)).toNat = 0 := by
    rw [hzero]
    rfl
  have hcond' := hcond
  rw [PatternedWordData.expectedWordAt_0] at hcond'
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor (PatternedWordData.expectedWordAt 0)
        (MachineState.readWord input 0)) := by
    rw [hzero]
    decide
  simp (config := { maxSteps := 300000 })
    [PrefixStatePaths.firstComparePath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, PrefixStateCodecopy.copiedState, firstMatchedState, rho,
      hword, hzero, hcond, hcond', hfalse, compare_mload_active s input,
      cond_match input hmatch, act_idem,
      UInt256.isTrue, hrun,
      PrefixStatePaths.pc4023, PrefixStatePaths.pc4024, PrefixStatePaths.pc4025,
      PrefixStatePaths.pc4026, PrefixStatePaths.pc4027,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]
  rfl

/-- The five-instruction first-word comparison on a word-0 mismatch: the
final `JUMPI` is taken to the generic compression entry at pc 464. -/
theorem run_firstCompare_mismatch (s : State) (input : ByteArray)
    (hne : MachineState.readWord input 0 ≠ PatternedWordData.expectedWordAt 0)
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
      (UInt256.xor (PatternedWordData.expectedWordAt 0)
        (MachineState.readWord input 0)) = true :=
    cond_mismatch input hne
  have hcond : (UInt256.xor (PatternedWordData.expectedWordAt 0)
      (MachineState.readWord input 0)).toNat ≠ 0 := by
    intro hz
    apply hne
    exact ((KnownInputLogic.wordXor_eq_zero_iff _ _).1
      (by apply Challenge.EvmProof.Word.word_ext; simpa using hz)).symm
  have hcond' := hcond
  rw [PatternedWordData.expectedWordAt_0] at hcond'
  simp (config := { maxSteps := 300000 })
    [PrefixStatePaths.firstComparePath, Stepper.runLocatedBlock, Stepper.runLocated,
      Stepper.runInstr, PrefixStateCodecopy.copiedState, DriverTrace.compressEntry, rho,
      hword, htrue, hcond, hcond', compare_mload_active s input,
      cond_mismatch input hne, act_idem, hdest,
      UInt256.isTrue, hrun, hcode,
      PrefixStatePaths.pc4023, PrefixStatePaths.pc4024, PrefixStatePaths.pc4025,
      PrefixStatePaths.pc4026, PrefixStatePaths.pc4027,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.mod_eq_of_lt]
  rfl

/-- The single generic `CODECOPY` step for block 0 through the provided
`PrefixStateCodecopy` lemma with the concrete five-word suffix. -/
def gasSteps_codecopy_first (s : State) (input : ByteArray)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (PrefixStateCodecopy.preCopyState s (rho input))
      (PrefixStateCodecopy.copiedState s (rho input)) :=
  PrefixStateCodecopy.gasSteps_codecopy s (rho input) (by simp [rho]) hcode hrun hnp

/-- Combined first-block execution certificate: nine setup instructions, the
`CODECOPY` step, and five comparison instructions, branching on the word-0
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
      (run_prefix s input hcalldata hcode hrun)
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
        (run_firstCompare_match s input hmatch hrun')
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
        (run_firstCompare_mismatch s input hmatch hcode hrun')
        hrun'
        (by
          change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
            s.executionEnv.fork s.executionEnv.codeAddr = false
          exact hnp)
    exact GasSteps.cast (gpre.trans (gcc.trans gcmp)) rfl (by rw [if_neg hmatch])

#print axioms gasSteps_first

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTraceFirst
