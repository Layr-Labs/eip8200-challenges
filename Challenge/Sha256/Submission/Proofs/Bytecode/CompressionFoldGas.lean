import Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGasBase

/-! Exact gas summaries for the feed-forward phase. -/

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas

open Challenge.Sha256
open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

theorem foldIteration_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat)
    (hi : i < 8) (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_foldIteration s msgOff returnDest rest i hi hcap
      hcode hfork hrun hnp).cost +
        MachineState.memCost (Compression.foldAt s msgOff returnDest rest i).activeWords.toNat =
      100 + MachineState.memCost
        (Compression.afterFoldIteration s msgOff returnDest rest i).activeWords.toNat := by
  have hcond := blockCost_potential_of_static Compression.foldConditionPath 24
    (Compression.run_foldCondition s msgOff returnDest rest i hi (by omega) hrun)
    (by simpa [Compression.foldAt, State.fork] using hfork)
    (by simp [Compression.foldConditionPath, CopyFree]) (by rfl)
  have hsetup := blockCost_potential_of_static Compression.foldSetupPath 55
    (Compression.run_foldSetup s msgOff returnDest rest i (by omega) hcode hrun)
    (by simpa [Compression.afterFoldCondition, Compression.foldAt, State.fork]
      using hfork)
    (by simp [Compression.foldSetupPath, CopyFree]) (by rfl)
  have qSetFork : (Compression.foldGotSet s msgOff returnDest rest i).fork =
      .Osaka := by
    simpa [Compression.foldGotSet, Compression.foldGotH,
      Compression.loadedSaved, Accessors.storeReturned,
      Accessors.loadReturned, State.fork] using hfork
  have hinc := blockCost_potential_of_static Compression.foldIncrementPath 21
    (Compression.run_foldIncrement s msgOff returnDest rest i hi (by omega)
      hcode hrun) qSetFork
    (by simp [Compression.foldIncrementPath, CopyFree]) (by rfl)
  simp only [Compression.gasSteps_foldIteration,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  omega

theorem foldLoop_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 988)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_foldLoop s msgOff returnDest rest hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.foldLoopState s msgOff returnDest rest 0).activeWords.toNat =
      8 * 100 + MachineState.memCost
        (Compression.foldLoopState s msgOff returnDest rest 8).activeWords.toNat := by
  unfold Compression.gasSteps_foldLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add 8 100
  intro i hi
  let q := Compression.foldLoopState s msgOff returnDest rest i
  have qcode : q.executionEnv.code = submissionBytecode := by simpa [q] using hcode
  have qfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have qrun : q.halt = .Running := by simpa [q] using hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have h := foldIteration_cost_potential q msgOff returnDest rest i hi hcap
    qcode qfork qrun qnp
  dsimp only [q] at h
  have h' :
      (Compression.gasSteps_foldIteration
        (Compression.foldLoopState s msgOff returnDest rest i)
        msgOff returnDest rest i hi hcap qcode qfork qrun qnp).cost +
          MachineState.memCost
            (Compression.foldLoopState s msgOff returnDest rest i).activeWords.toNat =
        100 + MachineState.memCost
          (Compression.foldLoopState s msgOff returnDest rest (i + 1)).activeWords.toNat := by
    simpa [Compression.foldAt, Compression.foldLoopState] using h
  simpa only [Challenge.EvmProof.GasSteps.cast_cost] using h'

theorem roundsExit_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (Compression.gasSteps_roundsExit s msgOff returnDest rest hcap hcode hfork
      hrun hnp).cost + MachineState.memCost
        (Compression.roundAt s msgOff returnDest rest 64).activeWords.toNat =
      29 + MachineState.memCost
        (Compression.foldAt s msgOff returnDest rest 0).activeWords.toNat := by
  have hresult := Compression.run_roundsExit s msgOff returnDest rest hcap
    hcode hrun
  have hmeter := blockCost_potential_of_static Compression.roundsExitPath 29
    hresult (by simpa [Compression.roundAt, State.fork] using hfork)
    (by simp [Compression.roundsExitPath, Compression.conditionPath, CopyFree])
    (by rfl)
  unfold Compression.gasSteps_roundsExit
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact hmeter

theorem foldExit_cost_potential (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    (Compression.gasSteps_foldExit s msgOff returnDest rest hcap hcode hfork
      hrun hnp hreturn).cost + MachineState.memCost
        (Compression.foldAt s msgOff returnDest rest 8).activeWords.toNat =
      37 + MachineState.memCost
        (Compression.compressReturned s returnDest rest).activeWords.toNat := by
  have hresult := Compression.run_foldExit s msgOff returnDest rest hcap
    hcode hrun hreturn
  have hmeter := blockCost_potential_of_static Compression.foldExitPath 37
    hresult (by simpa [Compression.foldAt, State.fork] using hfork)
    (by simp [Compression.foldExitPath, Compression.foldConditionPath, CopyFree])
    (by rfl)
  unfold Compression.gasSteps_foldExit
  simp only [Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  exact hmeter

end Challenge.Sha256.Submission.Proofs.Bytecode.CompressionGas
