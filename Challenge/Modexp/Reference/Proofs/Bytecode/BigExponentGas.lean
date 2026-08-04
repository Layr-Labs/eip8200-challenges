import Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Aggregate gas proofs for multi-limb exponentiation -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM

private theorem jump1000 :
    Decode.isValidJumpDest referenceBytecode 1000 = true :=
  Artifact.isValidJumpDest_index 756 (by rfl)

private theorem jump1015 :
    Decode.isValidJumpDest referenceBytecode 1015 = true :=
  Artifact.isValidJumpDest_index 763 (by rfl)

private theorem jump1034 :
    Decode.isValidJumpDest referenceBytecode 1034 = true :=
  Artifact.isValidJumpDest_index 772 (by rfl)

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

def gasSteps_exponentBit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest j)
      (afterSelectedBit s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) := by
  let frame := bitFrame accumulatorWord count b e m baseOff expOff i j offset
    byte (exponentBit byte j) rest
  have hframe : frame.length < 980 := by simp [frame, bitFrame]; omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka innerGuardPath
      (by simpa [innerLoop, Artifact.referenceArtifact] using hcode)
      (by simpa [innerLoop, State.fork] using hfork)
      (run_innerGuard s accumulatorWord count b e m baseOff expOff i j offset
        byte rest (by omega) hj hrun)
      (by simpa [innerLoop] using hrun)
      (by simpa [innerLoop, State.fork] using hnp)
  have htoSquare := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka innerToSquarePath
      (by simpa [innerBody, innerLoop, Artifact.referenceArtifact] using hcode)
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
    Artifact.referenceArtifact .Osaka squareToCopyPath
      (by simpa [Artifact.referenceArtifact] using hcode)
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
  have htoProduct := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka copyToProductPath
      (by simpa [Artifact.referenceArtifact] using hcode)
      (by simpa [State.fork] using hfork)
      (run_copyToProduct s accumulatorWord count b e m baseOff expOff i j offset
        byte rest (by omega) hcode hrun)
      (by simpa using hrun)
      (by simpa [State.fork] using hnp)
  have hproductRaw := BigMul.gasSteps_mulModBig
    (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset byte
      rest)
    2048 1024 3072 0 count 1034 frame hframe hcount
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa [State.fork] using hnp) jump1034
  have hproduct : Challenge.EvmProof.GasSteps
      (BigMul.mulEntry
        (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset
          byte rest) 2048 1024 3072 0 count 1034 frame)
      (productReturned s accumulatorWord count b e m baseOff expOff i j offset
        byte rest) := by
    simpa [productReturned, mulResult, frame] using hproductRaw
  have htoSelect := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.referenceArtifact .Osaka productToSelectPath
      (by simpa [Artifact.referenceArtifact] using hcode)
      (by simpa [State.fork] using hfork)
      (run_productToSelect s accumulatorWord count b e m baseOff expOff i j
        offset byte rest (by omega) hrun)
      (by simpa using hrun)
      (by simpa [State.fork] using hnp)
  have hselect := gasSteps_selection s accumulatorWord count b e m baseOff
    expOff i j offset byte rest (by omega) hcount hj hcode hfork hrun hnp
  exact hguard.trans <| htoSquare.trans <| hsquare.trans <|
    htoCopy.trans <| hcopy.trans <| htoProduct.trans <| hproduct.trans <|
    htoSelect.trans hselect

theorem gasSteps_exponentBit_cost_potential (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    (gasSteps_exponentBit s accumulatorWord count b e m baseOff expOff i j
      offset byte rest hcap hcount hj hcode hfork hrun hnp).cost +
        MachineState.memCost
          (innerLoop s accumulatorWord count b e m baseOff expOff i offset byte
            rest j).activeWords.toNat =
      (613 + count * 526 +
          2 * (count * (102 + 256 * (426 + count * 906)))) +
        MachineState.memCost
          (afterSelectedBit s accumulatorWord count b e m baseOff expOff i j
            offset byte rest).activeWords.toNat := by
  let frame := bitFrame accumulatorWord count b e m baseOff expOff i j offset
    byte (exponentBit byte j) rest
  have hframe : frame.length < 980 := by simp [frame, bitFrame]; omega
  have hguard :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      innerGuardPath 26
        (run_innerGuard s accumulatorWord count b e m baseOff expOff i j offset
          byte rest (by omega) hj hrun)
        (by simpa [innerLoop, State.fork] using hfork)
        (by native_decide) (by native_decide)
  have htoSquare :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      innerToSquarePath 49
        (run_innerToSquare s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hj hcode hrun)
        (by simpa [innerBody, innerLoop, State.fork] using hfork)
        (by native_decide) (by native_decide)
  have hsquare := BigMul.gasSteps_mulModBig_cost_potential
    (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j)
    2048 2048 3072 0 count 1000 frame hframe hcount
    (by simpa [innerBody, innerLoop] using hcode)
    (by simpa [innerBody, innerLoop, State.fork] using hfork)
    (by simpa [innerBody, innerLoop] using hrun)
    (by simpa [innerBody, innerLoop, State.fork] using hnp) jump1000
  have htoCopy :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      squareToCopyPath 24
        (run_squareToCopy s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hcode hrun)
        (by simpa [State.fork] using hfork)
        (by native_decide) (by native_decide)
  have hcopy := BigHelpers.gasSteps_copy_cost_potential
    (squareReturned s accumulatorWord count b e m baseOff expOff i j offset
      byte rest)
    2048 3072 count 1015 frame (by omega) hcount
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa [State.fork] using hnp) jump1015
  have htoProduct :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      copyToProductPath 29
        (run_copyToProduct s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hcode hrun)
        (by simpa [State.fork] using hfork)
        (by native_decide) (by native_decide)
  have hproduct := BigMul.gasSteps_mulModBig_cost_potential
    (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset byte
      rest)
    2048 1024 3072 0 count 1034 frame hframe hcount
    (by simpa using hcode) (by simpa [State.fork] using hfork)
    (by simpa using hrun) (by simpa [State.fork] using hnp) jump1034
  have htoSelect :=
    Challenge.EvmProof.Meter.runLocatedBlock_cost_potential_of_copyFree
      productToSelectPath 11
        (run_productToSelect s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hrun)
        (by simpa [State.fork] using hfork)
        (by native_decide) (by native_decide)
  have hselect := gasSteps_selection_cost_potential s accumulatorWord count b e
    m baseOff expOff i j offset byte rest (by omega) hcount hj hcode hfork hrun
    hnp
  unfold gasSteps_exponentBit
  simp only [id_eq, Challenge.EvmProof.GasSteps.trans_cost,
    Challenge.EvmProof.Stepper.runLocatedBlock_sound_cost]
  dsimp only [frame] at hguard htoSquare hsquare htoCopy hcopy htoProduct hproduct htoSelect hselect
  simp only [innerLoop, innerBody, squareEntry, squareReturned, mulResult,
    copiedSquare, productReturned, selectLoop, afterSelectedBit,
    BigMul.mulEntry, BigMul.mulReturned, BigHelpers.copyEntry,
    BigHelpers.copyReturned] at hguard htoSquare hsquare htoCopy hcopy htoProduct hproduct htoSelect hselect ⊢
  omega

end Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent
