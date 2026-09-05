import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentModels
import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryHotBlock
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

private theorem jump1289 :
    Decode.isValidJumpDest submissionBytecode 1289 = true :=
  Artifact.isValidJumpDest_index 964 (by rfl)

private theorem jump1316 :
    Decode.isValidJumpDest submissionBytecode 1316 = true :=
  Artifact.isValidJumpDest_index 978 (by rfl)

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
      (afterBitStep s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) := by
  let frame := bitFrame accumulatorWord count b e m baseOff expOff i j offset
    byte (exponentBit byte j) rest
  let tail := bitTailFrame accumulatorWord count b e m baseOff expOff i j
    offset byte rest
  have hframe : frame.length < 980 := by simp [frame, bitFrame]; omega
  have htail : tail.length < 980 := by simp [tail, bitTailFrame]; omega
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
  have hsquareRaw := MontgomeryHotBlock.gasSteps_hot
    (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j)
    (UInt256.ofNat 2048) count (UInt256.ofNat 1000) frame hframe hcount
    (by simp)
    (by simpa [innerBody, innerLoop] using hcode)
    (by simpa [innerBody, innerLoop, State.fork] using hfork)
    (by simpa [innerBody, innerLoop] using hrun)
    (by simpa [innerBody, innerLoop, State.fork] using hnp)
    (by simpa using jump1000)
  have hsquare : Challenge.EvmProof.GasSteps
      (squareEntry s accumulatorWord count b e m baseOff expOff i j offset byte
        rest)
      (squareReturned s accumulatorWord count b e m baseOff expOff i j offset
        byte rest) := by
    simpa [squareEntry, squareReturned, mulResult, frame, MontgomeryHotBlock.hotEntry,
      Challenge.EvmProof.Word.literal_eq_ofNat] using hsquareRaw
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
  have hredirect := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka redirectPath
      (by simpa [Artifact.submissionArtifact] using hcode)
      (by simpa [State.fork] using hfork)
      (run_redirect s accumulatorWord count b e m baseOff expOff i j offset
        byte rest (by omega) hcode hrun)
      (by simpa using hrun)
      (by simpa [State.fork] using hnp)
  by_cases hbit : (exponentBit byte j).toNat = 0
  · have hbranch : Challenge.EvmProof.GasSteps
        (bitBranch s accumulatorWord count b e m baseOff expOff i j offset byte
          rest)
        (bitZeroTail s accumulatorWord count b e m baseOff expOff i j offset
          byte rest) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka branchPath
          (by simpa [bitBranch, Artifact.submissionArtifact] using hcode)
          (by simpa [bitBranch, State.fork] using hfork)
          (run_branchZero s accumulatorWord count b e m baseOff expOff i j
            offset byte rest (by omega) hbit hrun)
          (by simpa [bitBranch] using hrun)
          (by simpa [bitBranch, State.fork] using hnp)
    have hstep : Challenge.EvmProof.GasSteps
        (bitZeroTail s accumulatorWord count b e m baseOff expOff i j offset
          byte rest)
        (innerLoop
          (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset
            byte rest)
          accumulatorWord count b e m baseOff expOff i offset byte rest
          (j + 1)) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka tailPath
          (by simpa [bitZeroTail, Artifact.submissionArtifact] using hcode)
          (by simpa [bitZeroTail, State.fork] using hfork)
          (run_tail
            (bitZeroTail s accumulatorWord count b e m baseOff expOff i j offset
              byte rest)
            accumulatorWord count b e m baseOff expOff i j offset byte rest
            (by omega) rfl rfl
            (by simpa [bitZeroTail] using hcode)
            (by simpa [bitZeroTail] using hrun))
          (by simpa [bitZeroTail] using hrun)
          (by simpa [bitZeroTail, State.fork] using hnp)
    exact Challenge.EvmProof.GasSteps.cast
      (hguard.trans <| htoSquare.trans <| hsquare.trans <| htoCopy.trans <|
        hcopy.trans <| hredirect.trans <| hbranch.trans hstep) rfl
      (by simp [afterBitStep, bitStepProgress, hbit])
  · have hbranch : Challenge.EvmProof.GasSteps
        (bitBranch s accumulatorWord count b e m baseOff expOff i j offset byte
          rest)
        (bitProductEntry s accumulatorWord count b e m baseOff expOff i j offset
          byte rest) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka branchPath
          (by simpa [bitBranch, Artifact.submissionArtifact] using hcode)
          (by simpa [bitBranch, State.fork] using hfork)
          (run_branchOne s accumulatorWord count b e m baseOff expOff i j
            offset byte rest (by omega) hbit hcode hrun)
          (by simpa [bitBranch] using hrun)
          (by simpa [bitBranch, State.fork] using hnp)
    have hcall := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka productCallPath
        (by simpa [bitProductEntry, Artifact.submissionArtifact] using hcode)
        (by simpa [bitProductEntry, State.fork] using hfork)
        (run_productCall s accumulatorWord count b e m baseOff expOff i j
          offset byte rest (by omega) hcode hrun)
        (by simpa [bitProductEntry] using hrun)
        (by simpa [bitProductEntry, State.fork] using hnp)
    have hproductRaw := MontgomeryHotBlock.gasSteps_hot
      (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset byte
        rest)
      (UInt256.ofNat 1024) count (UInt256.ofNat 1316) tail htail hcount
      (by simp)
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp)
      (by simpa using jump1316)
    have hproduct : Challenge.EvmProof.GasSteps
        (MontgomeryHotBlock.hotEntry
          (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset
            byte rest) (UInt256.ofNat 1024) count (UInt256.ofNat 1316) tail)
        (bitProductReturned s accumulatorWord count b e m baseOff expOff i j
          offset byte rest) := by
      simpa [bitProductReturned, mulResult, tail,
        Challenge.EvmProof.Word.literal_eq_ofNat] using hproductRaw
    have hcopyBack := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka copyBackPath
        (by simpa [Artifact.submissionArtifact] using hcode)
        (by simpa [State.fork] using hfork)
        (run_copyBack s accumulatorWord count b e m baseOff expOff i j offset
          byte rest (by omega) hcode hrun)
        (by simpa using hrun)
        (by simpa [State.fork] using hnp)
    have hcopyBackRaw := BigHelpers.gasSteps_copy
      (bitProductReturned s accumulatorWord count b e m baseOff expOff i j
        offset byte rest)
      2048 3072 count 1289 tail (by omega) hcount
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp) jump1289
    have hcopy2 : Challenge.EvmProof.GasSteps
        (BigHelpers.copyEntry
          (bitProductReturned s accumulatorWord count b e m baseOff expOff i j
            offset byte rest) 2048 3072 count 1289 tail)
        (bitCopyBack s accumulatorWord count b e m baseOff expOff i j offset
          byte rest) := by
      simpa [bitCopyBack, tail] using hcopyBackRaw
    have hpc : (bitCopyBack s accumulatorWord count b e m baseOff expOff i j
        offset byte rest).pc = UInt256.ofNat 1289 := by
      have h1289 : (1289 : UInt256) = UInt256.ofNat 1289 := by decide
      exact h1289
    have hstackEq : (bitCopyBack s accumulatorWord count b e m baseOff expOff i j
        offset byte rest).stack =
        bitTailFrame accumulatorWord count b e m baseOff expOff i j offset byte
          rest := by
      simp [bitCopyBack, BigHelpers.copyReturned]
    have hstep : Challenge.EvmProof.GasSteps
        (bitCopyBack s accumulatorWord count b e m baseOff expOff i j offset
          byte rest)
        (innerLoop
          (bitCopyBack s accumulatorWord count b e m baseOff expOff i j offset
            byte rest)
          accumulatorWord count b e m baseOff expOff i offset byte rest
          (j + 1)) :=
      Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka tailPath
          (by simpa [bitCopyBack, BigHelpers.copyReturned,
            Artifact.submissionArtifact] using hcode)
          (by simpa [bitCopyBack, BigHelpers.copyReturned, State.fork]
            using hfork)
          (run_tail
            (bitCopyBack s accumulatorWord count b e m baseOff expOff i j offset
              byte rest)
            accumulatorWord count b e m baseOff expOff i j offset byte rest
            (by omega) hpc hstackEq
            (by simpa [bitCopyBack, BigHelpers.copyReturned] using hcode)
            (by simpa [bitCopyBack, BigHelpers.copyReturned] using hrun))
          (by simpa [bitCopyBack, BigHelpers.copyReturned] using hrun)
          (by simpa [bitCopyBack, BigHelpers.copyReturned, State.fork]
            using hnp)
    exact Challenge.EvmProof.GasSteps.cast
      (hguard.trans <| htoSquare.trans <| hsquare.trans <| htoCopy.trans <|
        hcopy.trans <| hredirect.trans <| hbranch.trans <| hcall.trans <|
        hproduct.trans <| hcopyBack.trans <| hcopy2.trans hstep) rfl
      (by simp [afterBitStep, bitStepProgress, hbit])

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
  simpa [exponentBitLoopState, afterBitStep, exponentBitProgress, current]
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


section ColdPath
set_option linter.unusedVariables false

/-! ## S2 cold path: gas traces, shifted hot iterators, and the phase state -/

/-! ### Cold path gas traces -/

def gasSteps_coldStart (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1005)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentEntry s accumulatorWord count b e m baseOff expOff rest)
      (coldOuter s accumulatorWord count b e m baseOff expOff rest 0) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldStartPath
      (by simpa [exponentEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [exponentEntry, State.fork] using hfork)
      (run_coldStart s accumulatorWord count b e m baseOff expOff rest hcap hrun)
      (by simpa [exponentEntry] using hrun)
      (by simpa [exponentEntry, State.fork] using hnp)

def gasSteps_coldExitAt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1005) (he : e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (coldOuter s accumulatorWord count b e m baseOff expOff rest e)
      (coldExit s accumulatorWord count b e m baseOff expOff rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldGuardPath
      (by simpa [coldOuter, Artifact.submissionArtifact] using hcode)
      (by simpa [coldOuter, State.fork] using hfork)
      (run_coldGuardExit s accumulatorWord count b e m baseOff expOff rest hcap he hcode hrun)
      (by simpa [coldOuter] using hrun)
      (by simpa [coldOuter, State.fork] using hnp)

def gasSteps_hotExitAt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1005) (he : e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerLoop s accumulatorWord count b e m baseOff expOff rest e)
      (coldExit s accumulatorWord count b e m baseOff expOff rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerGuardPath
      (by simpa [outerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [outerLoop, State.fork] using hfork)
      (run_outerGuardExit s accumulatorWord count b e m baseOff expOff rest hcap he hcode hrun)
      (by simpa [outerLoop] using hrun)
      (by simpa [outerLoop, State.fork] using hnp)

def gasSteps_coldZeroByte (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1005) (he : e < 2 ^ 256) (hi : i < e)
    (hoff : expOff + i < 2 ^ 256) (hi256 : i + 1 < 2 ^ 256)
    (hzero : (loadedExponentByte s expOff i).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (coldOuter s accumulatorWord count b e m baseOff expOff rest i)
      (coldOuter s accumulatorWord count b e m baseOff expOff rest (i + 1)) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldGuardPath
      (by simpa [coldOuter, Artifact.submissionArtifact] using hcode)
      (by simpa [coldOuter, State.fork] using hfork)
      (run_coldGuard s accumulatorWord count b e m baseOff expOff i rest hcap he hi hrun)
      (by simpa [coldOuter] using hrun)
      (by simpa [coldOuter, State.fork] using hnp)).trans
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldLoadPath
      (by simpa [coldOuterBody, coldOuter, Artifact.submissionArtifact] using hcode)
      (by simpa [coldOuterBody, coldOuter, State.fork] using hfork)
      (run_coldLoad s accumulatorWord count b e m baseOff expOff i rest hcap hoff hrun)
      (by simpa [coldOuterBody, coldOuter] using hrun)
      (by simpa [coldOuterBody, coldOuter, State.fork] using hnp)).trans
      ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldTestZeroPath
      (by simpa [coldLoaded, coldByteFrame, Artifact.submissionArtifact] using hcode)
      (by simpa [coldLoaded, coldByteFrame, State.fork] using hfork)
      (run_coldTestZero s accumulatorWord count b e m baseOff expOff i (UInt256.ofNat (expOff + i)) (loadedExponentByte s expOff i) rest hcap hzero hcode hrun)
      (by simpa [coldLoaded, coldByteFrame] using hrun)
      (by simpa [coldLoaded, coldByteFrame, State.fork] using hnp)).trans
        (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldNextPath
      (by simpa [coldNextState, coldByteFrame, Artifact.submissionArtifact] using hcode)
      (by simpa [coldNextState, coldByteFrame, State.fork] using hfork)
      (run_coldNext s accumulatorWord count b e m baseOff expOff i (UInt256.ofNat (expOff + i)) (loadedExponentByte s expOff i) rest hcap hi256 hcode hrun)
      (by simpa [coldNextState, coldByteFrame] using hrun)
      (by simpa [coldNextState, coldByteFrame, State.fork] using hnp))))

def gasSteps_coldBytes (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff k : Nat) (rest : List UInt256)
    (hcap : rest.length < 1005) (he : e < 2 ^ 256) (hk : k ≤ e)
    (hoff : expOff + e < 2 ^ 256)
    (hzeros : ∀ t, t < k → (loadedExponentByte s expOff t).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (coldOuter s accumulatorWord count b e m baseOff expOff rest 0)
      (coldOuter s accumulatorWord count b e m baseOff expOff rest k) :=
  Challenge.EvmProof.GasSteps.iterateBounded (I := fun t =>
      coldOuter s accumulatorWord count b e m baseOff expOff rest t) k
    fun t ht =>
      gasSteps_coldZeroByte s accumulatorWord count b e m baseOff expOff t rest
        hcap he (by omega) (by omega) (by omega) (hzeros t ht) hcode hfork hrun hnp

def gasSteps_coldEnter (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1005) (he : e < 2 ^ 256) (hi : i < e)
    (hoff : expOff + i < 2 ^ 256)
    (hnz : ¬ (loadedExponentByte s expOff i).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (coldOuter s accumulatorWord count b e m baseOff expOff rest i)
      (coldBitLoop s accumulatorWord count b e m baseOff expOff i
        (UInt256.ofNat (expOff + i)) (loadedExponentByte s expOff i) rest 0) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldGuardPath
      (by simpa [coldOuter, Artifact.submissionArtifact] using hcode)
      (by simpa [coldOuter, State.fork] using hfork)
      (run_coldGuard s accumulatorWord count b e m baseOff expOff i rest hcap he hi hrun)
      (by simpa [coldOuter] using hrun)
      (by simpa [coldOuter, State.fork] using hnp)).trans
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldLoadPath
      (by simpa [coldOuterBody, coldOuter, Artifact.submissionArtifact] using hcode)
      (by simpa [coldOuterBody, coldOuter, State.fork] using hfork)
      (run_coldLoad s accumulatorWord count b e m baseOff expOff i rest hcap hoff hrun)
      (by simpa [coldOuterBody, coldOuter] using hrun)
      (by simpa [coldOuterBody, coldOuter, State.fork] using hnp)).trans
      (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldTestPath
      (by simpa [coldLoaded, coldByteFrame, Artifact.submissionArtifact] using hcode)
      (by simpa [coldLoaded, coldByteFrame, State.fork] using hfork)
      (run_coldTest s accumulatorWord count b e m baseOff expOff i (UInt256.ofNat (expOff + i)) (loadedExponentByte s expOff i) rest hcap hnz hrun)
      (by simpa [coldLoaded, coldByteFrame] using hrun)
      (by simpa [coldLoaded, coldByteFrame, State.fork] using hnp)))

def gasSteps_coldBitStep (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005) (hj : j < 8)
    (hbit : (exponentBit byte j).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (coldBitLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest j)
      (coldBitLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest (j + 1)) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldBitComputePath
      (by simpa [coldBitLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [coldBitLoop, State.fork] using hfork)
      (run_coldBitCompute s accumulatorWord count b e m baseOff expOff i j offset byte rest hcap hj hrun)
      (by simpa [coldBitLoop] using hrun)
      (by simpa [coldBitLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldBitZeroPath
      (by simpa [coldBitTest, coldBitLoop, bitFrame, Artifact.submissionArtifact] using hcode)
      (by simpa [coldBitTest, coldBitLoop, bitFrame, State.fork] using hfork)
      (run_coldBitZero s accumulatorWord count b e m baseOff expOff i j offset byte (exponentBit byte j) rest hcap hbit hcode hrun)
      (by simpa [coldBitTest, coldBitLoop, bitFrame] using hrun)
      (by simpa [coldBitTest, coldBitLoop, bitFrame, State.fork] using hnp))

def gasSteps_coldBits (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j0 : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005) (hj0 : j0 ≤ 8)
    (hbits : ∀ t, t < j0 → (exponentBit byte t).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (coldBitLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest 0)
      (coldBitLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest j0) :=
  Challenge.EvmProof.GasSteps.iterateBounded (I := fun t =>
      coldBitLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest t) j0
    fun t ht =>
      gasSteps_coldBitStep s accumulatorWord count b e m baseOff expOff i t
        offset byte rest hcap (by omega) (hbits t ht) hcode hfork hrun hnp

def gasSteps_coldHit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005) (hj : j < 8)
    (hcount : count < 2 ^ 256)
    (hbit : ¬ (exponentBit byte j).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (coldBitLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest j)
      (innerLoop
        (coldCopied s accumulatorWord count b e m baseOff expOff i offset byte
          rest j)
        accumulatorWord count b e m baseOff expOff i offset byte rest
        (j + 1)) := by
  have hframe : (bitTailFrame accumulatorWord count b e m baseOff expOff i j
      offset byte rest).length < 1016 := by
    simp [bitTailFrame]
    omega
  have hvalid : Decode.isValidJumpDest submissionBytecode
      ((1419 : UInt256)).toNat = true := by
    rw [show ((1419 : UInt256)).toNat = 1419 from by decide]
    exact jumpColdCopyRet
  have hstep0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldBitComputePath
      (by simpa [coldBitLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [coldBitLoop, State.fork] using hfork)
      (run_coldBitCompute s accumulatorWord count b e m baseOff expOff i j offset byte rest hcap hj hrun)
      (by simpa [coldBitLoop] using hrun)
      (by simpa [coldBitLoop, State.fork] using hnp)
  have hstep1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldBitHitPath
      (by simpa [coldBitTest, coldBitLoop, bitFrame, Artifact.submissionArtifact] using hcode)
      (by simpa [coldBitTest, coldBitLoop, bitFrame, State.fork] using hfork)
      (run_coldBitHit s accumulatorWord count b e m baseOff expOff i j offset byte (exponentBit byte j) rest hcap hbit hcode hrun)
      (by simpa [coldBitTest, coldBitLoop, bitFrame] using hrun)
      (by simpa [coldBitTest, coldBitLoop, bitFrame, State.fork] using hnp)
  have hstep2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldHitPath
      (by simpa [coldHitState, coldBitLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [coldHitState, coldBitLoop, State.fork] using hfork)
      (run_coldHit s accumulatorWord count b e m baseOff expOff i j offset byte rest hcap hcode hrun)
      (by simpa [coldHitState, coldBitLoop] using hrun)
      (by simpa [coldHitState, coldBitLoop, State.fork] using hnp)
  have hstep3 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldCopyCallPath
      (by simpa [coldCopyState, coldBitLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [coldCopyState, coldBitLoop, State.fork] using hfork)
      (run_coldCopyCall s accumulatorWord count b e m baseOff expOff i j offset byte rest hcap hcode hrun)
      (by simpa [coldCopyState, coldBitLoop] using hrun)
      (by simpa [coldCopyState, coldBitLoop, State.fork] using hnp)
  have hcopy := BigHelpers.gasSteps_copy
    (coldCopyState s accumulatorWord count b e m baseOff expOff i offset byte
      rest j)
    2048 1024 count 1419
    (bitTailFrame accumulatorWord count b e m baseOff expOff i j offset byte
      rest) hframe hcount
    (by simpa [coldCopyState, coldBitLoop] using hcode)
    (by simpa [coldCopyState, coldBitLoop, State.fork] using hfork)
    (by simpa [coldCopyState, coldBitLoop] using hrun)
    (by simpa [coldCopyState, coldBitLoop, State.fork] using hnp)
    hvalid
  have hret := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldCopyRetPath
      (by simpa [coldCopied, coldCopyState, coldBitLoop,
        BigHelpers.copyReturned, Artifact.submissionArtifact] using hcode)
      (by simpa [coldCopied, coldCopyState, coldBitLoop,
        BigHelpers.copyReturned, State.fork] using hfork)
      (run_coldCopyRet
        (coldCopied s accumulatorWord count b e m baseOff expOff i offset byte
          rest j)
        accumulatorWord count b e m baseOff expOff i j offset byte rest hcap
        (by
          simp [coldCopied, BigHelpers.copyReturned,
            show ((1419 : UInt256)) = UInt256.ofNat 1419 from by decide])
        (by simp [coldCopied, BigHelpers.copyReturned])
        (by simpa [coldCopied, coldCopyState, coldBitLoop,
          BigHelpers.copyReturned] using hcode)
        (by simpa [coldCopied, coldCopyState, coldBitLoop,
          BigHelpers.copyReturned] using hrun))
      (by simpa [coldCopied, coldCopyState, coldBitLoop,
        BigHelpers.copyReturned] using hrun)
      (by simpa [coldCopied, coldCopyState, coldBitLoop,
        BigHelpers.copyReturned, State.fork] using hnp)
  exact Challenge.EvmProof.GasSteps.cast
    (hstep0.trans (hstep1.trans (hstep2.trans (hstep3.trans (hcopy.trans hret)))))
    rfl rfl

/-! ### Shifted hot iterators (`gasSteps_exponentBit` / `gasSteps_exponentByte`
are already generic in the bit / byte index, so only the indexing wrapper is
new). -/

def gasSteps_bitAtFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i start t : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hcount : count < 2 ^ 256) (hj : start + t < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitLoopStateFrom s accumulatorWord count b e m baseOff expOff i offset
        byte rest start t)
      (bitLoopStateFrom s accumulatorWord count b e m baseOff expOff i offset
        byte rest start (t + 1)) := by
  let current := bitProgressFrom s accumulatorWord count b e m baseOff expOff i
    offset byte rest start t
  have hstep := gasSteps_exponentBit current accumulatorWord count b e m baseOff
    expOff i (start + t) offset byte rest hcap hcount hj
    (by simpa [current] using hcode)
    (by simpa [current, State.fork] using hfork)
    (by simpa [current] using hrun)
    (by simpa [current, State.fork] using hnp)
  exact Challenge.EvmProof.GasSteps.cast hstep
    (by simp [bitLoopStateFrom, current])
    (by
      simp [bitLoopStateFrom, afterBitStep, bitProgressFrom, current,
        Nat.add_assoc])

def gasSteps_bitsFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i start : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hcount : count < 2 ^ 256) (hstart : start ≤ 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitLoopStateFrom s accumulatorWord count b e m baseOff expOff i offset
        byte rest start 0)
      (bitLoopStateFrom s accumulatorWord count b e m baseOff expOff i offset
        byte rest start (8 - start)) :=
  Challenge.EvmProof.GasSteps.iterateBounded (I := fun t =>
      bitLoopStateFrom s accumulatorWord count b e m baseOff expOff i offset
        byte rest start t) (8 - start)
    fun t ht =>
      gasSteps_bitAtFrom s accumulatorWord count b e m baseOff expOff i start t
        offset byte rest hcap hcount (by omega) hcode hfork hrun hnp

/-- Generic inner-loop exit: `gasSteps_exponentByteFinish` with the accumulated
state left abstract. -/
def gasSteps_innerExitFrom (cur : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968) (hi : i + 1 < 2 ^ 256)
    (hcode : cur.executionEnv.code = submissionBytecode)
    (hfork : cur.fork = .Osaka) (hrun : cur.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig cur.executionEnv.precompileConfig cur.executionEnv.fork
      cur.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop cur accumulatorWord count b e m baseOff expOff i offset byte
        rest 8)
      (outerLoop cur accumulatorWord count b e m baseOff expOff rest (i + 1)) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka innerGuardPath
        (by simpa [innerLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [innerLoop, State.fork] using hfork)
        (run_innerFinishGuard cur accumulatorWord count b e m baseOff expOff i
          offset byte rest (by omega) hcode hrun)
        (by simpa [innerLoop] using hrun)
        (by simpa [innerLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka innerFinishPath
        (by simpa [innerExit, innerLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [innerExit, innerLoop, State.fork] using hfork)
        (run_innerFinish cur accumulatorWord count b e m baseOff expOff i
          offset byte rest (by omega) hi hcode hrun)
        (by simpa [innerExit, innerLoop] using hrun)
        (by simpa [innerExit, innerLoop, State.fork] using hnp))

def gasSteps_byteAtFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff start t : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hi : start + t < e) (hoff : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerStateFrom s accumulatorWord count b e m baseOff expOff rest start t)
      (outerStateFrom s accumulatorWord count b e m baseOff expOff rest start
        (t + 1)) := by
  let current := byteProgressFrom s accumulatorWord count b e m baseOff expOff
    rest start t
  have hstep := gasSteps_exponentByte current accumulatorWord count b e m baseOff
    expOff (start + t) rest hcap hcount he hi (by omega)
    (by simpa [current] using hcode)
    (by simpa [current, State.fork] using hfork)
    (by simpa [current] using hrun)
    (by simpa [current, State.fork] using hnp)
  exact Challenge.EvmProof.GasSteps.cast hstep
    (by simp [outerStateFrom, current])
    (by
      simp [outerStateFrom, afterExponentByte, byteProgressFrom, current,
        Nat.add_assoc])

def gasSteps_bytesFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff start : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hstart : start ≤ e) (hoff : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerStateFrom s accumulatorWord count b e m baseOff expOff rest start 0)
      (outerStateFrom s accumulatorWord count b e m baseOff expOff rest start
        (e - start)) :=
  Challenge.EvmProof.GasSteps.iterateBounded (I := fun t =>
      outerStateFrom s accumulatorWord count b e m baseOff expOff rest start t)
    (e - start)
    fun t ht =>
      gasSteps_byteAtFrom s accumulatorWord count b e m baseOff expOff start t
        rest hcap hcount he (by omega) hoff hcode hfork hrun hnp

def gasSteps_bitsFromTo8 (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i start : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 968)
    (hcount : count < 2 ^ 256) (hstart : start ≤ 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest start)
      (innerLoop
        (bitFinalFrom s accumulatorWord count b e m baseOff expOff i offset
          byte rest start)
        accumulatorWord count b e m baseOff expOff i offset byte rest 8) :=
  Challenge.EvmProof.GasSteps.cast
    (gasSteps_bitsFrom s accumulatorWord count b e m baseOff expOff i start
      offset byte rest hcap hcount hstart hcode hfork hrun hnp)
    (by simp [bitLoopStateFrom, bitProgressFrom])
    (by
      simp only [bitLoopStateFrom, bitFinalFrom]
      rw [show start + (8 - start) = 8 from by omega])

def gasSteps_bytesFromTo (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff start : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hstart : start ≤ e) (hoff : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerLoop s accumulatorWord count b e m baseOff expOff rest start)
      (outerLoop
        (byteFinalFrom s accumulatorWord count b e m baseOff expOff rest start)
        accumulatorWord count b e m baseOff expOff rest e) :=
  Challenge.EvmProof.GasSteps.cast
    (gasSteps_bytesFrom s accumulatorWord count b e m baseOff expOff start rest
      hcap hcount he hstart hoff hcode hfork hrun hnp)
    (by simp [outerStateFrom, byteProgressFrom])
    (by
      simp only [outerStateFrom, byteFinalFrom]
      rw [show start + (e - start) = e from by omega])

/-! ### The exponent phase: cold prefix followed by the hot loop -/

def gasSteps_exponentPhase (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 968) (hcount : count < 2 ^ 256)
    (he : e < 2 ^ 256) (hoff : expOff + e < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (exponentEntry s accumulatorWord count b e m baseOff expOff rest)
      (coldExit
        (exponentPhaseState s accumulatorWord count b e m baseOff expOff rest)
        accumulatorWord count b e m baseOff expOff rest) := by
  have hkle : coldByteIndex s expOff e ≤ e := coldByteIndex_le s expOff e
  have hstart := gasSteps_coldStart s accumulatorWord count b e m baseOff expOff
    rest (by omega) hcode hfork hrun hnp
  by_cases hk : coldByteIndex s expOff e = e
  · have hzeros : ∀ t, t < e → (loadedExponentByte s expOff t).toNat = 0 := by
      intro t ht
      exact coldByteIndex_zeros s expOff e t (by omega)
    have hbytes := gasSteps_coldBytes s accumulatorWord count b e m baseOff
      expOff e rest (by omega) he (Nat.le_refl e) hoff hzeros hcode hfork hrun
      hnp
    have hexit := gasSteps_coldExitAt s accumulatorWord count b e m baseOff
      expOff rest (by omega) he hcode hfork hrun hnp
    have hphase : exponentPhaseState s accumulatorWord count b e m baseOff
        expOff rest = s := by
      simp only [exponentPhaseState, if_pos hk]
    exact Challenge.EvmProof.GasSteps.cast
      (hstart.trans (hbytes.trans hexit)) rfl (by rw [hphase])
  · have hklt : coldByteIndex s expOff e < e := by omega
    have hnz := coldByteIndex_hit s expOff e hklt
    have hj0lt : coldPhaseBit s expOff e < 8 :=
      coldBitIndex_lt (coldPhaseByte s expOff e)
        (by
          simpa [coldPhaseByte] using
            loadedExponentByte_lt256 s expOff (coldByteIndex s expOff e))
        (by simpa [coldPhaseByte] using hnz)
    have hbitnz : ¬ (exponentBit (coldPhaseByte s expOff e)
        (coldPhaseBit s expOff e)).toNat = 0 :=
      coldBitIndex_hit (coldPhaseByte s expOff e) hj0lt
    have hzeros : ∀ t, t < coldByteIndex s expOff e →
        (loadedExponentByte s expOff t).toNat = 0 := by
      intro t ht
      exact coldByteIndex_zeros s expOff e t ht
    have hbits : ∀ t, t < coldPhaseBit s expOff e →
        (exponentBit (coldPhaseByte s expOff e) t).toNat = 0 := by
      intro t ht
      exact coldBitIndex_zeros (coldPhaseByte s expOff e) t ht
    have hbytes := gasSteps_coldBytes s accumulatorWord count b e m baseOff
      expOff (coldByteIndex s expOff e) rest (by omega) he hkle hoff hzeros
      hcode hfork hrun hnp
    have henter := gasSteps_coldEnter s accumulatorWord count b e m baseOff
      expOff (coldByteIndex s expOff e) rest (by omega) he hklt (by omega) hnz
      hcode hfork hrun hnp
    have hcoldbits := gasSteps_coldBits s accumulatorWord count b e m baseOff
      expOff (coldByteIndex s expOff e) (coldPhaseBit s expOff e)
      (coldPhaseOffset s expOff e) (coldPhaseByte s expOff e) rest (by omega)
      (by omega) hbits hcode hfork hrun hnp
    have hhit := gasSteps_coldHit s accumulatorWord count b e m baseOff expOff
      (coldByteIndex s expOff e) (coldPhaseBit s expOff e)
      (coldPhaseOffset s expOff e) (coldPhaseByte s expOff e) rest (by omega)
      hj0lt hcount hbitnz hcode hfork hrun hnp
    have hhotbits := gasSteps_bitsFromTo8
      (coldPhaseHit s accumulatorWord count b e m baseOff expOff rest)
      accumulatorWord count b e m baseOff expOff (coldByteIndex s expOff e)
      (coldPhaseStart s expOff e) (coldPhaseOffset s expOff e)
      (coldPhaseByte s expOff e) rest hcap hcount
      (by simp only [coldPhaseStart]; omega)
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa using hnp)
    have hfinish := gasSteps_innerExitFrom
      (coldPhaseBits s accumulatorWord count b e m baseOff expOff rest)
      accumulatorWord count b e m baseOff expOff (coldByteIndex s expOff e)
      (coldPhaseOffset s expOff e) (coldPhaseByte s expOff e) rest hcap
      (by omega) (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa using hnp)
    have hhotbytes := gasSteps_bytesFromTo
      (coldPhaseBits s accumulatorWord count b e m baseOff expOff rest)
      accumulatorWord count b e m baseOff expOff (coldByteIndex s expOff e + 1)
      rest hcap hcount he (by omega) hoff
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa using hnp)
    have hexit := gasSteps_hotExitAt
      (coldPhaseTail s accumulatorWord count b e m baseOff expOff rest)
      accumulatorWord count b e m baseOff expOff rest (by omega) he
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa using hnp)
    have hphase : exponentPhaseState s accumulatorWord count b e m baseOff
        expOff rest =
        coldPhaseTail s accumulatorWord count b e m baseOff expOff rest := by
      simp only [exponentPhaseState, if_neg hk]
    exact Challenge.EvmProof.GasSteps.cast
      (hstart.trans (hbytes.trans (henter.trans (hcoldbits.trans
        (hhit.trans (hhotbits.trans (hfinish.trans
          (hhotbytes.trans hexit)))))))) rfl (by rw [hphase])

end ColdPath

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
