import Challenge.Modexp.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

set_option linter.unusedSimpArgs false in
theorem run_baseTail_head (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseTailHeadPath
      (baseReturnedState input i base) =
        some (baseTailMidState input i base) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have h562 : (562 : UInt256).toNat = 562 := by decide
  have h562Word : (562 : UInt256) = UInt256.ofNat 562 := by decide
  have h256Word : (256 : UInt256) = UInt256.ofNat 256 := by decide
  simp (config := { maxSteps := 150000 })
    [baseTailHeadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseReturnedState, baseTailMidState, Accessors.calldataByteReturned,
      baseRest, baseLoopState, baseStep, byteWord, Accessors.calldataByteValue,
      nonzeroState, callerRest, Dispatch.wordEntryState, Main.headerState,
      initialState, wordPCs, List.exchange,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hi256, h562, h562Word, h256Word]

set_option linter.unusedSimpArgs false in
theorem run_baseTail_swap (input : ByteArray) (i : Nat) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseTailSwapPath
      (baseTailMidState input i base) =
        some (baseTailSwappedState input i base) := by
  simp (config := { maxSteps := 100000 })
    [baseTailSwapPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseTailMidState, baseTailSwappedState, baseLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      wordPCs, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_baseTail_pop (input : ByteArray) (i : Nat) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseTailPopPath
      (baseTailSwappedState input i base) =
        some (baseTailPoppedState input i base) := by
  simp (config := { maxSteps := 100000 })
    [baseTailPopPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseTailSwappedState, baseTailPoppedState, baseLoopState, nonzeroState,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      wordPCs]

set_option linter.unusedSimpArgs false in
theorem run_baseTail_finish (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseTailFinishPath
      (baseTailPoppedState input i base) =
        some (baseLoopState input (i + 1) (baseStep input i base)) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hi256 : i < 2 ^ 256 := by omega
  have h541 : (541 : UInt256).toNat = 541 := by decide
  have h541Word : (541 : UInt256) = UInt256.ofNat 541 := by decide
  have hisucc' := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) (by omega : i + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat i =
      UInt256.ofNat (i + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hisucc'
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp (config := { maxSteps := 150000 })
    [baseTailFinishPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseTailPoppedState, baseLoopState, nonzeroState, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState, wordPCs,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      hi256, h541, h541Word, honeWord, jump541, hisucc', hincLeft]

theorem run_baseTail (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseTailPath
      (baseReturnedState input i base) =
        some (baseLoopState input (i + 1) (baseStep input i base)) := by
  unfold baseTailPath
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    baseTailHeadPath (baseTailSwapPath ++ baseTailPopPath ++ baseTailFinishPath)
    (baseReturnedState input i base) (baseTailMidState input i base)
    (baseLoopState input (i + 1) (baseStep input i base))
    (run_baseTail_head input i base hvalid hi) rfl
    (Challenge.EvmProof.Stepper.runLocatedBlock_append
      baseTailSwapPath (baseTailPopPath ++ baseTailFinishPath)
      (baseTailMidState input i base) (baseTailSwappedState input i base)
      (baseLoopState input (i + 1) (baseStep input i base))
      (run_baseTail_swap input i base) rfl
      (Challenge.EvmProof.Stepper.runLocatedBlock_append
        baseTailPopPath baseTailFinishPath
        (baseTailSwappedState input i base) (baseTailPoppedState input i base)
        (baseLoopState input (i + 1) (baseStep input i base))
        (run_baseTail_pop input i base) rfl
        (run_baseTail_finish input i base hvalid hi)))

def gasSteps_baseIteration (input : ByteArray) (i : Nat) (base : UInt256)
    (hvalid : ValidInput input) (hi : i < baseSize input) :
    Challenge.EvmProof.GasSteps (baseLoopState input i base)
      (baseLoopState input (i + 1) (baseStep input i base)) := by
  have h562 : (562 : UInt256).toNat = 562 := by decide
  have hcap : (baseRest input i base).length < 1017 := by
    simp [baseRest, callerRest]
  have hjump : Decode.isValidJumpDest submissionBytecode
      (562 : UInt256).toNat = true := by
    rw [h562]
    exact jump562
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseGuardPath rfl rfl
        (run_baseGuard input i base hvalid hi) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseCallPath rfl rfl
        (run_baseCall input i base hvalid hi) rfl
        deployAddress_not_precompile).trans <|
    (Accessors.gasSteps_calldataByte (baseLoopState input i base)
      (UInt256.ofNat (96 + i)) 0 562 (baseRest input i base)
      hcap rfl rfl rfl deployAddress_not_precompile hjump).trans <|
    Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka baseTailPath rfl rfl
        (run_baseTail input i base hvalid hi) rfl deployAddress_not_precompile

def gasSteps_baseLoop (input : ByteArray) (hvalid : ValidInput input) :
    Challenge.EvmProof.GasSteps (baseLoopState input 0 0)
      (baseLoopState input (baseSize input) (baseAfter input (baseSize input))) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (baseSize input)
    (fun i hi => gasSteps_baseIteration input i (baseAfter input i) hvalid hi)

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
