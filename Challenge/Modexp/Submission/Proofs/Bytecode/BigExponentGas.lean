import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Aggregate gas proofs for multi-limb exponentiation -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM

private theorem jump1000 :
    Decode.isValidJumpDest submissionBytecode 1000 = true :=
  Artifact.isValidJumpDest_index 756 (by rfl)

private theorem jump1015 :
    Decode.isValidJumpDest submissionBytecode 1015 = true :=
  Artifact.isValidJumpDest_index 763 (by rfl)

private theorem jump1034 :
    Decode.isValidJumpDest submissionBytecode 1040 = true :=
  Artifact.isValidJumpDest_index 776 (by rfl)

def gasSteps_selectIteration (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hk : k < count)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectLoop s accumulatorWord count b e m baseOff expOff i j k offset
        byte rest)
      (selectLoop s accumulatorWord count b e m baseOff expOff i j (k + 1)
        offset byte rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectGuardPath
      (by simpa [selectLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [selectLoop, State.fork] using hfork)
      (run_selectGuard s accumulatorWord count b e m baseOff expOff i j k
        offset byte rest (by omega) hcount hk hrun)
      (by simpa [selectLoop] using hrun)
      (by simpa [selectLoop, State.fork] using hnp)
  have hbody := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectBodyPath
      (by simpa [selectBody, selectLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [selectBody, selectLoop, State.fork] using hfork)
      (run_selectBody s accumulatorWord count b e m baseOff expOff i j k
        offset byte rest (by omega) (by omega) hcode hrun)
      (by simpa [selectBody, selectLoop] using hrun)
      (by simpa [selectBody, selectLoop, State.fork] using hnp)
  exact hguard.trans hbody

theorem gasSteps_selectIteration_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j k : Nat)
    (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hk : k < count) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_selectIteration s accumulatorWord count b e m baseOff expOff i j
      k offset byte rest hcap hcount hk hcode hfork hrun hnp).cost +
        MachineState.memCost
          (selectLoop s accumulatorWord count b e m baseOff expOff i j k
            offset byte rest).activeWords.toNat =
      123 + MachineState.memCost
        (selectLoop s accumulatorWord count b e m baseOff expOff i j (k + 1)
          offset byte rest).activeWords.toNat := by
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      selectGuardPath 26
        (run_selectGuard s accumulatorWord count b e m baseOff expOff i j k
          offset byte rest (by omega) hcount hk hrun)
        (by simpa [selectLoop, State.fork] using hfork)
        (by decide) (by decide)
  have hbody :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      selectBodyPath 97
        (run_selectBody s accumulatorWord count b e m baseOff expOff i j k
          offset byte rest (by omega) (by omega) hcode hrun)
        (by simpa [selectBody, selectLoop, State.fork] using hfork)
        (by decide) (by decide)
  unfold gasSteps_selectIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [selectLoop, selectBody] at hguard hbody ⊢
  omega

def gasSteps_selectLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectLoop s accumulatorWord count b e m baseOff expOff i j 0 offset
        byte rest)
      (selectLoop s accumulatorWord count b e m baseOff expOff i j count offset
        byte rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded count fun k hk =>
    gasSteps_selectIteration s accumulatorWord count b e m baseOff expOff i j
      k offset byte rest hcap hcount hk hcode hfork hrun hnp

theorem gasSteps_selectLoop_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_selectLoop s accumulatorWord count b e m baseOff expOff i j
      offset byte rest hcap hcount hcode hfork hrun hnp).cost +
        MachineState.memCost
          (selectLoop s accumulatorWord count b e m baseOff expOff i j 0
            offset byte rest).activeWords.toNat =
      count * 123 + MachineState.memCost
        (selectLoop s accumulatorWord count b e m baseOff expOff i j count
          offset byte rest).activeWords.toNat := by
  unfold gasSteps_selectLoop
  apply Challenge.EvmProof.Meter.iterateBounded_cost_potential_add
  intro k hk
  simpa [Nat.mul_comm] using
    gasSteps_selectIteration_cost_potential s accumulatorWord count b e m
      baseOff expOff i j k offset byte rest hcap hcount hk hcode hfork hrun hnp

def gasSteps_selectFinish (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectLoop s accumulatorWord count b e m baseOff expOff i j count offset
        byte rest)
      (afterSelectedBit s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectGuardPath
      (by simpa [selectLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [selectLoop, State.fork] using hfork)
      (run_selectFinishGuard s accumulatorWord count b e m baseOff expOff i j
        offset byte rest (by omega) hcount hcode hrun)
      (by simpa [selectLoop] using hrun)
      (by simpa [selectLoop, State.fork] using hnp)
  have hfinish := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectFinishPath
      (by simpa [selectExit, selectLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [selectExit, selectLoop, State.fork] using hfork)
      (run_selectFinish s accumulatorWord count b e m baseOff expOff i j offset
        byte rest (by omega) hj hcode hrun)
      (by simpa [selectExit, selectLoop] using hrun)
      (by simpa [selectExit, selectLoop, State.fork] using hnp)
  exact hguard.trans hfinish

theorem gasSteps_selectFinish_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_selectFinish s accumulatorWord count b e m baseOff expOff i j
      offset byte rest hcap hcount hj hcode hfork hrun hnp).cost +
        MachineState.memCost
          (selectLoop s accumulatorWord count b e m baseOff expOff i j count
            offset byte rest).activeWords.toNat =
      58 + MachineState.memCost
        (afterSelectedBit s accumulatorWord count b e m baseOff expOff i j
          offset byte rest).activeWords.toNat := by
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      selectGuardPath 26
        (run_selectFinishGuard s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hcount hcode hrun)
        (by simpa [selectLoop, State.fork] using hfork)
        (by decide) (by decide)
  have hfinish :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      selectFinishPath 32
        (run_selectFinish s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hj hcode hrun)
        (by simpa [selectExit, selectLoop, State.fork] using hfork)
        (by decide) (by decide)
  unfold gasSteps_selectFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [selectLoop, selectExit, afterSelectedBit, innerLoop] at hguard hfinish ⊢
  omega

def gasSteps_selection (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectLoop s accumulatorWord count b e m baseOff expOff i j 0 offset
        byte rest)
      (afterSelectedBit s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) :=
  (gasSteps_selectLoop s accumulatorWord count b e m baseOff expOff i j offset
    byte rest hcap hcount hcode hfork hrun hnp).trans
  (gasSteps_selectFinish s accumulatorWord count b e m baseOff expOff i j
    offset byte rest hcap hcount hj hcode hfork hrun hnp)

theorem gasSteps_selection_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_selection s accumulatorWord count b e m baseOff expOff i j offset
      byte rest hcap hcount hj hcode hfork hrun hnp).cost +
        MachineState.memCost
          (selectLoop s accumulatorWord count b e m baseOff expOff i j 0
            offset byte rest).activeWords.toNat =
      (count * 123 + 58) + MachineState.memCost
        (afterSelectedBit s accumulatorWord count b e m baseOff expOff i j
          offset byte rest).activeWords.toNat := by
  exact Challenge.EvmProof.Meter.gasSteps_trans_cost_potential
    (gasSteps_selectLoop s accumulatorWord count b e m baseOff expOff i j
      offset byte rest hcap hcount hcode hfork hrun hnp)
    (gasSteps_selectFinish s accumulatorWord count b e m baseOff expOff i j
      offset byte rest hcap hcount hj hcode hfork hrun hnp)
    (count * 123) 58
    (gasSteps_selectLoop_cost_potential s accumulatorWord count b e m baseOff
      expOff i j offset byte rest hcap hcount hcode hfork hrun hnp)
    (gasSteps_selectFinish_cost_potential s accumulatorWord count b e m baseOff
      expOff i j offset byte rest hcap hcount hj hcode hfork hrun hnp)

def gasSteps_selectSkippedIteration (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hk : k < count)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectSkippedLoop s accumulatorWord count b e m baseOff expOff i j k
        offset byte rest)
      (selectSkippedLoop s accumulatorWord count b e m baseOff expOff i j
        (k + 1) offset byte rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectGuardPath
      (by simpa [selectSkippedLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [selectSkippedLoop, State.fork] using hfork)
      (run_selectSkippedGuard s accumulatorWord count b e m baseOff expOff i j
        k offset byte rest (by omega) hcount hk hrun)
      (by simpa [selectSkippedLoop] using hrun)
      (by simpa [selectSkippedLoop, State.fork] using hnp)
  have hbody := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectBodyPath
      (by simpa [selectSkippedBody, selectSkippedLoop,
        Artifact.submissionArtifact] using hcode)
      (by simpa [selectSkippedBody, selectSkippedLoop, State.fork] using hfork)
      (run_selectSkippedBody s accumulatorWord count b e m baseOff expOff i j
        k offset byte rest (by omega) (by omega) hcode hrun)
      (by simpa [selectSkippedBody, selectSkippedLoop] using hrun)
      (by simpa [selectSkippedBody, selectSkippedLoop, State.fork] using hnp)
  exact hguard.trans hbody

def gasSteps_selectSkippedLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectSkippedLoop s accumulatorWord count b e m baseOff expOff i j 0
        offset byte rest)
      (selectSkippedLoop s accumulatorWord count b e m baseOff expOff i j
        count offset byte rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded count fun k hk =>
    gasSteps_selectSkippedIteration s accumulatorWord count b e m baseOff
      expOff i j k offset byte rest hcap hcount hk hcode hfork hrun hnp

def gasSteps_selectSkippedFinish (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectSkippedLoop s accumulatorWord count b e m baseOff expOff i j
        count offset byte rest)
      (afterSelectedBitSkip s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectGuardPath
      (by simpa [selectSkippedLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [selectSkippedLoop, State.fork] using hfork)
      (run_selectSkippedFinishGuard s accumulatorWord count b e m baseOff
        expOff i j offset byte rest (by omega) hcount hcode hrun)
      (by simpa [selectSkippedLoop] using hrun)
      (by simpa [selectSkippedLoop, State.fork] using hnp)
  have hfinish := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka selectFinishPath
      (by simpa [selectSkippedExit, selectSkippedLoop,
        Artifact.submissionArtifact] using hcode)
      (by simpa [selectSkippedExit, selectSkippedLoop, State.fork] using hfork)
      (run_selectSkippedFinish s accumulatorWord count b e m baseOff expOff i j
        offset byte rest (by omega) hj hcode hrun)
      (by simpa [selectSkippedExit, selectSkippedLoop] using hrun)
      (by simpa [selectSkippedExit, selectSkippedLoop, State.fork] using hnp)
  exact hguard.trans hfinish

def gasSteps_selectionSkipped (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectSkippedLoop s accumulatorWord count b e m baseOff expOff i j 0
        offset byte rest)
      (afterSelectedBitSkip s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) :=
  (gasSteps_selectSkippedLoop s accumulatorWord count b e m baseOff expOff i j
    offset byte rest hcap hcount hcode hfork hrun hnp).trans
  (gasSteps_selectSkippedFinish s accumulatorWord count b e m baseOff expOff
    i j offset byte rest hcap hcount hj hcode hfork hrun hnp)

def gasSteps_exponentBit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest j)
      (innerLoop (bitStepProgress s accumulatorWord count b e m baseOff
        expOff i j offset byte rest) accumulatorWord count b e m baseOff
        expOff i offset byte rest (j + 1)) := by
  let frame := bitFrame accumulatorWord count b e m baseOff expOff i j offset
    byte (exponentBit byte j) rest
  have hframe : frame.length < 980 := by simp [frame, bitFrame]; omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerGuardPath
      (by simpa [innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerLoop, State.fork] using hfork)
      (run_innerGuard s accumulatorWord count b e m baseOff expOff i j offset
        byte rest (by omega) hj hrun)
      (by simpa [innerLoop] using hrun)
      (by simpa [innerLoop, State.fork] using hnp)
  have htoSquare := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerToSquarePath
      (by simpa [innerBody, innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerBody, innerLoop, State.fork] using hfork)
      (run_innerToSquare s accumulatorWord count b e m baseOff expOff i j offset
        byte rest (by omega) hj hcode hrun)
      (by simpa [innerBody, innerLoop] using hrun)
      (by simpa [innerBody, innerLoop, State.fork] using hnp)
  have hsquareRaw := BigMul.gasSteps_mulModBig
    (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j)
    2048 2048 3072 0 count 1000 frame hframe hcount
    (by simpa [innerBody, innerLoop] using hcode)
    (by simpa [innerBody, innerLoop, State.fork] using hfork)
    (by simpa [innerBody, innerLoop] using hrun)
    (by simpa [innerBody, innerLoop, State.fork] using hnp) jump1000
  have hsquare : Challenge.EvmProof.GasSteps
      (squareEntry s accumulatorWord count b e m baseOff expOff i j offset byte
        rest)
      (squareReturned s accumulatorWord count b e m baseOff expOff i j offset
        byte rest) := by
    simpa [squareEntry, squareReturned, mulResult, frame] using hsquareRaw
  have htoCopy := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka squareToCopyPath
      (by simpa [Artifact.submissionArtifact] using hcode)
      (by simpa [State.fork] using hfork)
      (run_squareToCopy s accumulatorWord count b e m baseOff expOff i j offset
        byte rest (by omega) hcode hrun)
      (by simpa using hrun)
      (by simpa [State.fork] using hnp)
  have hcopyRaw := BigHelpers.gasSteps_copy
    (squareReturned s accumulatorWord count b e m baseOff expOff i j offset
      byte rest)
    2048 3072 count 1015 frame (by omega) hcount
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa [State.fork] using hnp) jump1015
  have hcopy : Challenge.EvmProof.GasSteps
      (BigHelpers.copyEntry
        (squareReturned s accumulatorWord count b e m baseOff expOff i j offset
          byte rest) 2048 3072 count 1015 frame)
      (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset byte
        rest) := by
    simpa [copiedSquare, frame] using hcopyRaw
  by_cases hbit : (exponentBit byte j).toNat = 0
  · have hbranch := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyToBranchPath
        (by simpa [copiedSquare, BigHelpers.copyReturned,
          Artifact.submissionArtifact] using hcode)
        (by simpa [copiedSquare, BigHelpers.copyReturned, State.fork]
          using hfork)
        (run_copyToBranchTaken s accumulatorWord count b e m baseOff expOff i
          j offset byte rest (by omega) hbit hcode hrun)
        (by simpa [copiedSquare, BigHelpers.copyReturned] using hrun)
        (by simpa [copiedSquare, BigHelpers.copyReturned, State.fork]
          using hnp)
    have htoSelectSkip := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka productToSelectPath
        (by simpa [skippedProduct, Artifact.submissionArtifact] using hcode)
        (by simpa [skippedProduct, State.fork] using hfork)
        (run_skippedToSelect s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hrun)
        (by simpa [skippedProduct] using hrun)
        (by simpa [skippedProduct, State.fork] using hnp)
    have hselectSkip := gasSteps_selectionSkipped s accumulatorWord count b e
      m baseOff expOff i j offset byte rest (by omega) hcount hj hcode hfork
      hrun hnp
    have h := hguard.trans <| htoSquare.trans <| hsquare.trans <|
      htoCopy.trans <| hcopy.trans <| hbranch.trans <|
      htoSelectSkip.trans hselectSkip
    simpa [bitStepProgress, afterSelectedBitSkip, hbit] using h
  · have htoProduct := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyToProductPath
        (by simpa [Artifact.submissionArtifact] using hcode)
        (by simpa [State.fork] using hfork)
        (run_copyToProduct s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hbit hcode hrun)
        (by simpa using hrun)
        (by simpa [State.fork] using hnp)
    have hproductRaw := BigMul.gasSteps_mulModBig
      (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset byte
        rest)
      2048 1024 3072 0 count 1040 frame hframe hcount
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp) jump1034
    have hproduct : Challenge.EvmProof.GasSteps
        (BigMul.mulEntry
          (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset
            byte rest) 2048 1024 3072 0 count 1040 frame)
        (productReturned s accumulatorWord count b e m baseOff expOff i j offset
          byte rest) := by
      simpa [productReturned, mulResult, frame] using hproductRaw
    have htoSelect := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka productToSelectPath
        (by simpa [Artifact.submissionArtifact] using hcode)
        (by simpa [State.fork] using hfork)
        (run_productToSelect s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hrun)
        (by simpa using hrun)
        (by simpa [State.fork] using hnp)
    have hselect := gasSteps_selection s accumulatorWord count b e m baseOff
      expOff i j offset byte rest (by omega) hcount hj hcode hfork hrun hnp
    have h := hguard.trans <| htoSquare.trans <| hsquare.trans <|
      htoCopy.trans <| hcopy.trans <| htoProduct.trans <| hproduct.trans <|
      htoSelect.trans hselect
    simpa [bitStepProgress, afterSelectedBit, hbit] using h


def exponentBitProgress (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => s
  | j + 1 =>
      bitStepProgress
        (exponentBitProgress s accumulatorWord count b e m baseOff expOff i
          offset byte rest j)
        accumulatorWord count b e m baseOff expOff i j offset byte rest

@[simp] theorem exponentBitProgress_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (exponentBitProgress s accumulatorWord count b e m baseOff expOff i offset
      byte rest j).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih => simp [exponentBitProgress, ih]

@[simp] theorem exponentBitProgress_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (exponentBitProgress s accumulatorWord count b e m baseOff expOff i offset
      byte rest j).halt = s.halt := by
  induction j with
  | zero => rfl
  | succ j ih => simp [exponentBitProgress, ih]

def exponentBitLoopState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  innerLoop
    (exponentBitProgress s accumulatorWord count b e m baseOff expOff i offset
      byte rest j)
    accumulatorWord count b e m baseOff expOff i offset byte rest j

def gasSteps_exponentBitAt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentBitLoopState s accumulatorWord count b e m baseOff expOff i
        offset byte rest j)
      (exponentBitLoopState s accumulatorWord count b e m baseOff expOff i
        offset byte rest (j + 1)) := by
  let current := exponentBitProgress s accumulatorWord count b e m baseOff
    expOff i offset byte rest j
  have hstep := gasSteps_exponentBit current accumulatorWord count b e m baseOff
    expOff i j offset byte rest hcap hcount hj
    (by simpa [current] using hcode)
    (by simpa [current, State.fork] using hfork)
    (by simpa [current] using hrun)
    (by simpa [current, State.fork] using hnp)
  simpa [exponentBitLoopState, afterSelectedBit, afterSelectedBitSkip,
    bitStepProgress, exponentBitProgress, current]
    using hstep


def gasSteps_exponentBits (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentBitLoopState s accumulatorWord count b e m baseOff expOff i
        offset byte rest 0)
      (exponentBitLoopState s accumulatorWord count b e m baseOff expOff i
        offset byte rest 8) :=
  Challenge.EvmProof.GasSteps.iterateBounded 8 fun j hj =>
    gasSteps_exponentBitAt s accumulatorWord count b e m baseOff expOff i j
      offset byte rest hcap hcount hj hcode hfork hrun hnp


def afterExponentByte (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  outerLoop
    (exponentBitProgress s accumulatorWord count b e m baseOff expOff i offset
      byte rest 8)
    accumulatorWord count b e m baseOff expOff rest (i + 1)

def gasSteps_exponentByteFinish (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968)
    (_hcount : count < 2 ^ 256) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentBitLoopState s accumulatorWord count b e m baseOff expOff i
        offset byte rest 8)
      (afterExponentByte s accumulatorWord count b e m baseOff expOff i offset
        byte rest) := by
  let current := exponentBitProgress s accumulatorWord count b e m baseOff
    expOff i offset byte rest 8
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerGuardPath
      (by simpa [exponentBitLoopState, innerLoop, current,
        Artifact.submissionArtifact] using hcode)
      (by simpa [exponentBitLoopState, innerLoop, current, State.fork] using hfork)
      (run_innerFinishGuard current accumulatorWord count b e m baseOff expOff i
        offset byte rest (by omega) (by simpa [current] using hcode)
        (by simpa [current] using hrun))
      (by simpa [exponentBitLoopState, innerLoop, current] using hrun)
      (by simpa [exponentBitLoopState, innerLoop, current, State.fork] using hnp)
  have hfinish := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerFinishPath
      (by simpa [innerExit, innerLoop, current,
        Artifact.submissionArtifact] using hcode)
      (by simpa [innerExit, innerLoop, current, State.fork] using hfork)
      (run_innerFinish current accumulatorWord count b e m baseOff expOff i
        offset byte rest (by omega) hi (by simpa [current] using hcode)
        (by simpa [current] using hrun))
      (by simpa [innerExit, innerLoop, current] using hrun)
      (by simpa [innerExit, innerLoop, current, State.fork] using hnp)
  exact Challenge.EvmProof.GasSteps.cast (hguard.trans hfinish)
    (by simp [exponentBitLoopState, current])
    (by simp [afterExponentByte, current])

theorem gasSteps_exponentByteFinish_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_exponentByteFinish s accumulatorWord count b e m baseOff expOff i
      offset byte rest hcap hcount hi hcode hfork hrun hnp).cost +
        MachineState.memCost
          (exponentBitLoopState s accumulatorWord count b e m baseOff expOff i
            offset byte rest 8).activeWords.toNat =
      58 + MachineState.memCost
        (afterExponentByte s accumulatorWord count b e m baseOff expOff i offset
          byte rest).activeWords.toNat := by
  let current := exponentBitProgress s accumulatorWord count b e m baseOff
    expOff i offset byte rest 8
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      innerGuardPath 26
        (run_innerFinishGuard current accumulatorWord count b e m baseOff expOff
          i offset byte rest (by omega) (by simpa [current] using hcode)
          (by simpa [current] using hrun))
        (by simpa [exponentBitLoopState, innerLoop, current, State.fork]
          using hfork)
        (by decide) (by decide)
  have hfinish :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      innerFinishPath 32
        (run_innerFinish current accumulatorWord count b e m baseOff expOff i
          offset byte rest (by omega) hi (by simpa [current] using hcode)
          (by simpa [current] using hrun))
        (by simpa [innerExit, innerLoop, current, State.fork] using hfork)
        (by decide) (by decide)
  unfold gasSteps_exponentByteFinish
  simp only [Challenge.EvmProof.GasSteps.cast_cost,
    Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [exponentBitLoopState, innerExit, innerLoop, afterExponentByte,
    outerLoop, current] at hguard hfinish ⊢
  omega

def gasSteps_exponentByte (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hi : i < e) (hoff : expOff + i < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerLoop s accumulatorWord count b e m baseOff expOff rest i)
      (afterExponentByte s accumulatorWord count b e m baseOff expOff i
        (UInt256.ofNat (expOff + i)) (loadedExponentByte s expOff i) rest) := by
  let offset := UInt256.ofNat (expOff + i)
  let byte := loadedExponentByte s expOff i
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerGuardPath
      (by simpa [outerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [outerLoop, State.fork] using hfork)
      (run_outerGuard s accumulatorWord count b e m baseOff expOff i rest
        (by omega) he hi hrun)
      (by simpa [outerLoop] using hrun)
      (by simpa [outerLoop, State.fork] using hnp)
  have hload := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerToInnerPath
      (by simpa [outerBody, outerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [outerBody, outerLoop, State.fork] using hfork)
      (run_outerToInner s accumulatorWord count b e m baseOff expOff i rest
        (by omega) hoff hrun)
      (by simpa [outerBody, outerLoop] using hrun)
      (by simpa [outerBody, outerLoop, State.fork] using hnp)
  have hbits := gasSteps_exponentBits s accumulatorWord count b e m baseOff
    expOff i offset byte rest hcap hcount hcode hfork hrun hnp
  have hfinish := gasSteps_exponentByteFinish s accumulatorWord count b e m
    baseOff expOff i offset byte rest hcap hcount (by omega) hcode hfork hrun hnp
  exact Challenge.EvmProof.GasSteps.cast
    (hguard.trans (hload.trans (hbits.trans hfinish))) rfl
    (by simp [afterExponentByte, offset, byte])


def exponentByteProgress (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : Nat → State
  | 0 => s
  | i + 1 =>
      let before := exponentByteProgress s accumulatorWord count b e m baseOff
        expOff rest i
      let offset := UInt256.ofNat (expOff + i)
      let byte := loadedExponentByte before expOff i
      exponentBitProgress before accumulatorWord count b e m baseOff expOff i
        offset byte rest 8

@[simp] theorem exponentByteProgress_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (rest : List UInt256) :
    (exponentByteProgress s accumulatorWord count b e m baseOff expOff rest
      i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [exponentByteProgress, ih]

@[simp] theorem exponentByteProgress_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i : Nat)
    (rest : List UInt256) :
    (exponentByteProgress s accumulatorWord count b e m baseOff expOff rest
      i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [exponentByteProgress, ih]

def exponentOuterState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  outerLoop
    (exponentByteProgress s accumulatorWord count b e m baseOff expOff rest i)
    accumulatorWord count b e m baseOff expOff rest i

def gasSteps_exponentByteAt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hi : i < e) (hoff : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentOuterState s accumulatorWord count b e m baseOff expOff rest i)
      (exponentOuterState s accumulatorWord count b e m baseOff expOff rest
        (i + 1)) := by
  let current := exponentByteProgress s accumulatorWord count b e m baseOff
    expOff rest i
  have hstep := gasSteps_exponentByte current accumulatorWord count b e m baseOff
    expOff i rest hcap hcount he hi (by omega)
    (by simpa [current] using hcode)
    (by simpa [current, State.fork] using hfork)
    (by simpa [current] using hrun)
    (by simpa [current, State.fork] using hnp)
  simpa [exponentOuterState, afterExponentByte, exponentByteProgress, current]
    using hstep


def gasSteps_exponentLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hoff : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentOuterState s accumulatorWord count b e m baseOff expOff rest 0)
      (exponentOuterState s accumulatorWord count b e m baseOff expOff rest e) :=
  Challenge.EvmProof.GasSteps.iterateBounded e fun i hi =>
    gasSteps_exponentByteAt s accumulatorWord count b e m baseOff expOff i rest
      hcap hcount he hi hoff hcode hfork hrun hnp


end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
