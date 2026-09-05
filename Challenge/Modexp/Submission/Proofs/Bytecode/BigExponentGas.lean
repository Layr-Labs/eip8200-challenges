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
    have hproductRaw := BigMul.gasSteps_mulModBig
      (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset byte
        rest)
      2048 1024 3072 0 count 1316 tail htail hcount
      (by simpa using hcode) (by simpa [State.fork] using hfork)
      (by simpa using hrun) (by simpa [State.fork] using hnp) jump1316
    have hproduct : Challenge.EvmProof.GasSteps
        (BigMul.mulEntry
          (copiedSquare s accumulatorWord count b e m baseOff expOff i j offset
            byte rest) 2048 1024 3072 0 count 1316 tail)
        (bitProductReturned s accumulatorWord count b e m baseOff expOff i j
          offset byte rest) := by
      simpa [bitProductReturned, mulResult, tail] using hproductRaw
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
