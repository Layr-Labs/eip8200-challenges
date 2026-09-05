import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
import Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
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


section ColdPath
set_option linter.unusedVariables false

/-! ## S2 cold path: gas traces, shifted hot iterators, and the phase state -/

/-- Index of the first nonzero exponent byte at or after `i`, bounded by `fuel`. -/
def coldScan (s : State) (expOff : Nat) : Nat → Nat → Nat
  | i, 0 => i
  | i, fuel + 1 =>
      if (loadedExponentByte s expOff i).toNat = 0 then
        coldScan s expOff (i + 1) fuel
      else i

/-- Index of the first nonzero exponent byte, or `e` if the exponent is zero. -/
def coldByteIndex (s : State) (expOff e : Nat) : Nat := coldScan s expOff 0 e

/-- Index of the first set bit of `byte` at or after `j`, bounded by `fuel`. -/
def coldBitScan (byte : UInt256) : Nat → Nat → Nat
  | j, 0 => j
  | j, fuel + 1 =>
      if (exponentBit byte j).toNat = 0 then coldBitScan byte (j + 1) fuel else j

/-- Index of the first set bit of `byte`, or `8` if `byte` is zero. -/
def coldBitIndex (byte : UInt256) : Nat := coldBitScan byte 0 8

theorem coldScan_le (s : State) (expOff fuel : Nat) :
    ∀ i, coldScan s expOff i fuel ≤ i + fuel := by
  induction fuel with
  | zero => intro i; simp [coldScan]
  | succ fuel ih =>
      intro i
      by_cases hz : (loadedExponentByte s expOff i).toNat = 0
      · rw [coldScan, if_pos hz]
        have := ih (i + 1)
        omega
      · rw [coldScan, if_neg hz]
        omega

theorem coldScan_zeros (s : State) (expOff fuel : Nat) :
    ∀ i t, i ≤ t → t < coldScan s expOff i fuel →
      (loadedExponentByte s expOff t).toNat = 0 := by
  induction fuel with
  | zero => intro i t _ hhi; rw [coldScan] at hhi; omega
  | succ fuel ih =>
      intro i t hlo hhi
      by_cases hz : (loadedExponentByte s expOff i).toNat = 0
      · rw [coldScan, if_pos hz] at hhi
        rcases Nat.lt_or_ge t (i + 1) with h | h
        · have ht : t = i := by omega
          subst ht
          exact hz
        · exact ih (i + 1) t h hhi
      · rw [coldScan, if_neg hz] at hhi; omega

theorem coldScan_hit (s : State) (expOff fuel : Nat) :
    ∀ i, coldScan s expOff i fuel < i + fuel →
      ¬ (loadedExponentByte s expOff (coldScan s expOff i fuel)).toNat = 0 := by
  induction fuel with
  | zero => intro i hlt; rw [coldScan] at hlt; omega
  | succ fuel ih =>
      intro i hlt
      by_cases hz : (loadedExponentByte s expOff i).toNat = 0
      · rw [coldScan, if_pos hz] at hlt ⊢
        exact ih (i + 1) (by omega)
      · rw [coldScan, if_neg hz] at hlt ⊢
        exact hz

theorem coldByteIndex_le (s : State) (expOff e : Nat) :
    coldByteIndex s expOff e ≤ e := by
  have := coldScan_le s expOff e 0
  simpa [coldByteIndex] using this

theorem coldByteIndex_zeros (s : State) (expOff e t : Nat)
    (ht : t < coldByteIndex s expOff e) :
    (loadedExponentByte s expOff t).toNat = 0 :=
  coldScan_zeros s expOff e 0 t (Nat.zero_le t) ht

theorem coldByteIndex_hit (s : State) (expOff e : Nat)
    (hlt : coldByteIndex s expOff e < e) :
    ¬ (loadedExponentByte s expOff (coldByteIndex s expOff e)).toNat = 0 :=
  coldScan_hit s expOff e 0 (by simpa [coldByteIndex] using hlt)

theorem coldBitScan_le (byte : UInt256) (fuel : Nat) :
    ∀ j, coldBitScan byte j fuel ≤ j + fuel := by
  induction fuel with
  | zero => intro j; simp [coldBitScan]
  | succ fuel ih =>
      intro j
      by_cases hz : (exponentBit byte j).toNat = 0
      · rw [coldBitScan, if_pos hz]
        have := ih (j + 1)
        omega
      · rw [coldBitScan, if_neg hz]
        omega

theorem coldBitScan_zeros (byte : UInt256) (fuel : Nat) :
    ∀ j t, j ≤ t → t < coldBitScan byte j fuel →
      (exponentBit byte t).toNat = 0 := by
  induction fuel with
  | zero => intro j t _ hhi; rw [coldBitScan] at hhi; omega
  | succ fuel ih =>
      intro j t hlo hhi
      by_cases hz : (exponentBit byte j).toNat = 0
      · rw [coldBitScan, if_pos hz] at hhi
        rcases Nat.lt_or_ge t (j + 1) with h | h
        · have ht : t = j := by omega
          subst ht
          exact hz
        · exact ih (j + 1) t h hhi
      · rw [coldBitScan, if_neg hz] at hhi; omega

theorem coldBitIndex_le (byte : UInt256) : coldBitIndex byte ≤ 8 := by
  have := coldBitScan_le byte 8 0
  simpa [coldBitIndex] using this

theorem coldBitIndex_zeros (byte : UInt256) (t : Nat)
    (ht : t < coldBitIndex byte) : (exponentBit byte t).toNat = 0 :=
  coldBitScan_zeros byte 8 0 t (Nat.zero_le t) ht

/-- Bridge between the machine-level bit extraction and its `Nat` model. -/
theorem exponentBit_toNat_eq_bitNat (byte : UInt256) (j : Nat) (hj : j < 8) :
    (exponentBit byte j).toNat = WordCorrect.exponentBitNat byte j := by
  have h := congrArg UInt256.toNat (WordCorrect.exponentBit_eq byte j hj)
  have hbit := WordCorrect.exponentBitNat_zero_or_one byte j
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : WordCorrect.exponentBitNat byte j < 2 ^ 256)]
    at h
  exact h

theorem bitPrefix_eq_zero (byte : UInt256) (n : Nat)
    (hz : ∀ j, j < n → WordCorrect.exponentBitNat byte j = 0) :
    WordCorrect.bitPrefix byte n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [WordCorrect.bitPrefix, ih (fun j hj => hz j (by omega)),
        hz n (by omega)]

theorem loadedExponentByte_lt256 (s : State) (expOff i : Nat) :
    (loadedExponentByte s expOff i).toNat < 256 := by
  unfold loadedExponentByte UInt256.byteAt
  rw [show (0 : UInt256).toNat = 0 by decide]
  rw [if_neg (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  have hand :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 ≤ 255 := Nat.and_le_right
  have hlt :
      ((MachineState.readWord s.executionEnv.calldata (expOff + i)).toNat >>>
        (8 * (31 - 0))) &&& 255 < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  omega

/-- A nonzero byte has a set bit, so the cold bit search terminates. -/
theorem coldBitIndex_lt (byte : UInt256) (hbyte : byte.toNat < 256)
    (hnz : ¬ byte.toNat = 0) : coldBitIndex byte < 8 := by
  rcases Nat.lt_or_ge (coldBitIndex byte) 8 with h | h
  · exact h
  · exfalso
    have h8 : coldBitIndex byte = 8 :=
      Nat.le_antisymm (coldBitIndex_le byte) h
    have hz : ∀ j, j < 8 → WordCorrect.exponentBitNat byte j = 0 := by
      intro j hj
      rw [← exponentBit_toNat_eq_bitNat byte j hj]
      exact coldBitIndex_zeros byte j (by omega)
    have hpre := bitPrefix_eq_zero byte 8 hz
    rw [WordCorrect.bitPrefix_eight byte hbyte] at hpre
    exact hnz hpre

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
    (hbit : ¬ (exponentBit byte j).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (coldBitLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest j)
      (innerLoop s accumulatorWord count b e m baseOff expOff i offset byte
        rest j) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldBitComputePath
      (by simpa [coldBitLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [coldBitLoop, State.fork] using hfork)
      (run_coldBitCompute s accumulatorWord count b e m baseOff expOff i j offset byte rest hcap hj hrun)
      (by simpa [coldBitLoop] using hrun)
      (by simpa [coldBitLoop, State.fork] using hnp)).trans
    ((Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldBitHitPath
      (by simpa [coldBitTest, coldBitLoop, bitFrame, Artifact.submissionArtifact] using hcode)
      (by simpa [coldBitTest, coldBitLoop, bitFrame, State.fork] using hfork)
      (run_coldBitHit s accumulatorWord count b e m baseOff expOff i j offset byte (exponentBit byte j) rest hcap hbit hcode hrun)
      (by simpa [coldBitTest, coldBitLoop, bitFrame] using hrun)
      (by simpa [coldBitTest, coldBitLoop, bitFrame, State.fork] using hnp)).trans
      (Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka coldHitPath
      (by simpa [coldHitState, coldBitLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [coldHitState, coldBitLoop, State.fork] using hfork)
      (run_coldHit s accumulatorWord count b e m baseOff expOff i j offset byte rest hcap hcode hrun)
      (by simpa [coldHitState, coldBitLoop] using hrun)
      (by simpa [coldHitState, coldBitLoop, State.fork] using hnp)))

/-- S2a: the hot inner loop resumes at the bit that was found. -/
abbrev coldHitTarget (s : State) (_accumulatorWord : UInt256)
    (_count _b _e _m _baseOff _expOff _i : Nat) (_offset _byte : UInt256)
    (_rest : List UInt256) (_j : Nat) : State := s

/-! ### Shifted hot iterators (`gasSteps_exponentBit` / `gasSteps_exponentByte`
are already generic in the bit / byte index, so only the indexing wrapper is
new). -/

def bitProgressFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (start : Nat) : Nat → State
  | 0 => s
  | t + 1 =>
      bitStepProgress
        (bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset
          byte rest start t)
        accumulatorWord count b e m baseOff expOff i (start + t) offset byte rest

@[simp] theorem bitProgressFrom_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i start t : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset byte
      rest start t).executionEnv = s.executionEnv := by
  induction t with
  | zero => rfl
  | succ t ih => simp [bitProgressFrom, ih]

@[simp] theorem bitProgressFrom_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i start t : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset byte
      rest start t).halt = s.halt := by
  induction t with
  | zero => rfl
  | succ t ih => simp [bitProgressFrom, ih]

def bitLoopStateFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (start t : Nat) : State :=
  innerLoop
    (bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset byte
      rest start t)
    accumulatorWord count b e m baseOff expOff i offset byte rest (start + t)

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

def byteProgressFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (start : Nat) : Nat → State
  | 0 => s
  | t + 1 =>
      let before := byteProgressFrom s accumulatorWord count b e m baseOff
        expOff rest start t
      exponentBitProgress before accumulatorWord count b e m baseOff expOff
        (start + t) (UInt256.ofNat (expOff + (start + t)))
        (loadedExponentByte before expOff (start + t)) rest 8

@[simp] theorem byteProgressFrom_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff start t : Nat)
    (rest : List UInt256) :
    (byteProgressFrom s accumulatorWord count b e m baseOff expOff rest start
      t).executionEnv = s.executionEnv := by
  induction t with
  | zero => rfl
  | succ t ih => simp [byteProgressFrom, ih]

@[simp] theorem byteProgressFrom_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff start t : Nat)
    (rest : List UInt256) :
    (byteProgressFrom s accumulatorWord count b e m baseOff expOff rest start
      t).halt = s.halt := by
  induction t with
  | zero => rfl
  | succ t ih => simp [byteProgressFrom, ih]

def outerStateFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (start t : Nat) : State :=
  outerLoop
    (byteProgressFrom s accumulatorWord count b e m baseOff expOff rest start t)
    accumulatorWord count b e m baseOff expOff rest (start + t)

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

theorem coldBitScan_hit (byte : UInt256) (fuel : Nat) :
    ∀ j, coldBitScan byte j fuel < j + fuel →
      ¬ (exponentBit byte (coldBitScan byte j fuel)).toNat = 0 := by
  induction fuel with
  | zero => intro j hlt; rw [coldBitScan] at hlt; omega
  | succ fuel ih =>
      intro j hlt
      by_cases hz : (exponentBit byte j).toNat = 0
      · rw [coldBitScan, if_pos hz] at hlt ⊢
        exact ih (j + 1) (by omega)
      · rw [coldBitScan, if_neg hz] at hlt ⊢
        exact hz

theorem coldBitIndex_hit (byte : UInt256) (h : coldBitIndex byte < 8) :
    ¬ (exponentBit byte (coldBitIndex byte)).toNat = 0 :=
  coldBitScan_hit byte 8 0 (by exact h)

/-- Accumulated state after running the hot bit loop from `start` to 8. -/
def bitFinalFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (start : Nat) : State :=
  bitProgressFrom s accumulatorWord count b e m baseOff expOff i offset byte
    rest start (8 - start)

/-- Accumulated state after running the hot byte loop from `start` to `e`. -/
def byteFinalFrom (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (start : Nat) : State :=
  byteProgressFrom s accumulatorWord count b e m baseOff expOff rest start
    (e - start)

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

/-- The exponent byte the cold search stops on. -/
def coldPhaseByte (s : State) (expOff e : Nat) : UInt256 :=
  loadedExponentByte s expOff (coldByteIndex s expOff e)

/-- The bit index the cold search stops on. -/
def coldPhaseBit (s : State) (expOff e : Nat) : Nat :=
  coldBitIndex (coldPhaseByte s expOff e)

/-- Calldata offset of the exponent byte the cold search stops on. -/
def coldPhaseOffset (s : State) (expOff e : Nat) : UInt256 :=
  UInt256.ofNat (expOff + coldByteIndex s expOff e)

/-- S2a: the cold search writes no memory, so the hot loop resumes from the
entry state. -/
def coldPhaseHit (s : State) (_accumulatorWord : UInt256)
    (_count _b _e _m _baseOff _expOff : Nat) (_rest : List UInt256) : State := s

/-- S2a resumes the hot inner loop at the bit that was found. -/
def coldPhaseStart (s : State) (expOff e : Nat) : Nat := coldPhaseBit s expOff e

/-- Memory state after finishing the byte the cold search stopped on. -/
def coldPhaseBits (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  bitFinalFrom (coldPhaseHit s accumulatorWord count b e m baseOff expOff rest)
    accumulatorWord count b e m baseOff expOff (coldByteIndex s expOff e)
    (coldPhaseOffset s expOff e) (coldPhaseByte s expOff e) rest
    (coldPhaseStart s expOff e)

/-- Memory state after the remaining hot exponent bytes. -/
def coldPhaseTail (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  byteFinalFrom (coldPhaseBits s accumulatorWord count b e m baseOff expOff rest)
    accumulatorWord count b e m baseOff expOff rest (coldByteIndex s expOff e + 1)

/-- Memory state after the whole exponent phase.  For an all-zero exponent the
cold path writes nothing, so the state is unchanged. -/
def exponentPhaseState (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  if coldByteIndex s expOff e = e then s
  else coldPhaseTail s accumulatorWord count b e m baseOff expOff rest

@[simp] theorem coldPhaseHit_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (coldPhaseHit s accumulatorWord count b e m baseOff expOff
      rest).executionEnv = s.executionEnv := by
  simp [coldPhaseHit]

@[simp] theorem coldPhaseHit_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) :
    (coldPhaseHit s accumulatorWord count b e m baseOff expOff rest).halt =
      s.halt := by
  simp [coldPhaseHit]

@[simp] theorem coldPhaseBits_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (coldPhaseBits s accumulatorWord count b e m baseOff expOff
      rest).executionEnv = s.executionEnv := by
  simp [coldPhaseBits, bitFinalFrom]

@[simp] theorem coldPhaseBits_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) :
    (coldPhaseBits s accumulatorWord count b e m baseOff expOff rest).halt =
      s.halt := by
  simp [coldPhaseBits, bitFinalFrom]

@[simp] theorem coldPhaseTail_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (coldPhaseTail s accumulatorWord count b e m baseOff expOff
      rest).executionEnv = s.executionEnv := by
  simp [coldPhaseTail, byteFinalFrom]

@[simp] theorem coldPhaseTail_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) :
    (coldPhaseTail s accumulatorWord count b e m baseOff expOff rest).halt =
      s.halt := by
  simp [coldPhaseTail, byteFinalFrom]

@[simp] theorem exponentPhaseState_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (exponentPhaseState s accumulatorWord count b e m baseOff expOff
      rest).executionEnv = s.executionEnv := by
  unfold exponentPhaseState
  split
  · rfl
  · simp

@[simp] theorem exponentPhaseState_halt (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff : Nat)
    (rest : List UInt256) :
    (exponentPhaseState s accumulatorWord count b e m baseOff expOff
      rest).halt = s.halt := by
  unfold exponentPhaseState
  split
  · rfl
  · simp

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
      hj0lt hbitnz hcode hfork hrun hnp
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
