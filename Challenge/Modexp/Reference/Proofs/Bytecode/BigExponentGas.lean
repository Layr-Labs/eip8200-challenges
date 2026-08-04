import Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Aggregate gas proofs for multi-limb exponentiation -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM

def gasSteps_selectIteration (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hk : k < count)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectLoop s accumulatorWord count b e m baseOff expOff i j k offset
        byte rest)
      (selectLoop s accumulatorWord count b e m baseOff expOff i j (k + 1)
        offset byte rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka selectGuardPath
      (by simpa [selectLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [selectLoop, State.fork] using hfork)
      (run_selectGuard s accumulatorWord count b e m baseOff expOff i j k
        offset byte rest (by omega) hcount hk hrun)
      (by simpa [selectLoop] using hrun)
      (by simpa [selectLoop, State.fork] using hnp)
  have hbody := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka selectBodyPath
      (by simpa [selectBody, selectLoop, Artifact.referenceArtifact] using hcode)
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
    (hk : k < count) (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
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
        (by native_decide) (by native_decide)
  have hbody :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      selectBodyPath 97
        (run_selectBody s accumulatorWord count b e m baseOff expOff i j k
          offset byte rest (by omega) (by omega) hcode hrun)
        (by simpa [selectBody, selectLoop, State.fork] using hfork)
        (by native_decide) (by native_decide)
  unfold gasSteps_selectIteration
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [selectLoop, selectBody] at hguard hbody ⊢
  omega

def gasSteps_selectLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
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
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
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
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (selectLoop s accumulatorWord count b e m baseOff expOff i j count offset
        byte rest)
      (afterSelectedBit s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka selectGuardPath
      (by simpa [selectLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [selectLoop, State.fork] using hfork)
      (run_selectFinishGuard s accumulatorWord count b e m baseOff expOff i j
        offset byte rest (by omega) hcount hcode hrun)
      (by simpa [selectLoop] using hrun)
      (by simpa [selectLoop, State.fork] using hnp)
  have hfinish := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka selectFinishPath
      (by simpa [selectExit, selectLoop, Artifact.referenceArtifact] using hcode)
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
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
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
        (by native_decide) (by native_decide)
  have hfinish :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      selectFinishPath 32
        (run_selectFinish s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hj hcode hrun)
        (by simpa [selectExit, selectLoop, State.fork] using hfork)
        (by native_decide) (by native_decide)
  unfold gasSteps_selectFinish
  simp only [Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  simp only [selectLoop, selectExit, afterSelectedBit, innerLoop] at hguard hfinish ⊢
  omega

def gasSteps_selection (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
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
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
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

end Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent
