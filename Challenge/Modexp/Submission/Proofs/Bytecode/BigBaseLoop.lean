import Challenge.Modexp.Submission.Proofs.Bytecode.BigBase
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Certified outer base-conversion loop

The directly loaded prefix already occupies the first `direct` base bytes, so
the reducing loop starts at index `direct` and runs `baseSize - direct` times.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseLoop

open EvmSemantics
open EvmSemantics.EVM
open BigBase

/-- Bitwise Horner over the base bytes `start, start+1, …` -/
def baseProgressFrom (count baseOff start : Nat) : Nat → State → State
  | 0, s => s
  | i + 1, s =>
      let before := baseProgressFrom count baseOff start i s
      bitProgress count (loadedBaseByte before baseOff (start + i)) 8 before

@[simp] theorem baseProgressFrom_halt (count baseOff start i : Nat) (s : State) :
    (baseProgressFrom count baseOff start i s).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [baseProgressFrom, ih]

@[simp] theorem baseProgressFrom_executionEnv (count baseOff start i : Nat)
    (s : State) :
    (baseProgressFrom count baseOff start i s).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [baseProgressFrom, ih]

@[simp] theorem baseProgressFrom_activeFork (count baseOff start i : Nat)
    (s : State) :
    (baseProgressFrom count baseOff start i s).fork = s.fork := by
  simp [State.fork]

@[simp] theorem loadedBaseByte_baseProgressFrom (count baseOff start i j : Nat)
    (s : State) :
    loadedBaseByte (baseProgressFrom count baseOff start j s) baseOff i =
      loadedBaseByte s baseOff i := by
  simp [loadedBaseByte]

def loopState (entry : State) (accumulator : UInt256)
    (count baseSize baseOff direct : Nat) (tail : List UInt256) (i : Nat) :
    State :=
  outerLoop (baseProgressFrom count baseOff direct i entry) accumulator count
    baseSize tail (direct + i)

def gasSteps_loopIteration (entry : State) (accumulator : UInt256)
    (count baseSize e m baseOff direct i : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256) (hi : direct + i < baseSize)
    (hoff : baseOff + baseSize < 2 ^ 256)
    (hcode : entry.executionEnv.code = submissionBytecode)
    (hfork : entry.fork = .Osaka) (hrun : entry.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig entry.executionEnv.precompileConfig
      entry.executionEnv.fork entry.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loopState entry accumulator count baseSize baseOff direct
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) i)
      (loopState entry accumulator count baseSize baseOff direct
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)
        (i + 1)) := by
  have hstep := gasSteps_baseByte
    (baseProgressFrom count baseOff direct i entry) accumulator count baseSize
    e m baseOff (direct + i) rest hcap hcount hbase hi (by omega)
    (by simpa using hcode) (by simpa using hfork) (by simpa using hrun)
    (by simpa [State.fork] using hnp)
  exact Challenge.EvmProof.GasSteps.cast hstep rfl
    (by simp [loopState, baseProgressFrom, Nat.add_assoc])

def gasSteps_loop (entry : State) (accumulator : UInt256)
    (count baseSize e m baseOff direct : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256) (hdirect : direct ≤ baseSize)
    (hoff : baseOff + baseSize < 2 ^ 256)
    (hcode : entry.executionEnv.code = submissionBytecode)
    (hfork : entry.fork = .Osaka) (hrun : entry.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig entry.executionEnv.precompileConfig
      entry.executionEnv.fork entry.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loopState entry accumulator count baseSize baseOff direct
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) 0)
      (loopState entry accumulator count baseSize baseOff direct
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)
        (baseSize - direct)) :=
  Challenge.EvmProof.GasSteps.iterateBounded (baseSize - direct) fun i hi =>
    gasSteps_loopIteration entry accumulator count baseSize e m baseOff direct i
      rest hcap hcount hbase (by omega) hoff hcode hfork hrun hnp

def convertedExit (entry : State) (accumulator : UInt256)
    (count baseSize baseOff direct : Nat) (tail : List UInt256) : State :=
  outerExit (baseProgressFrom count baseOff direct (baseSize - direct) entry)
    accumulator count baseSize tail baseSize

def initialAccumulator (entry : State) (accumulator : UInt256)
    (count baseSize baseOff direct : Nat) (tail : List UInt256) : State :=
  BigHelpers.addReturned
    (convertedExit entry accumulator count baseSize baseOff direct tail)
    2048 3072 1 0 count 944
    ([accumulator, UInt256.ofNat count, UInt256.ofNat baseSize] ++ tail)

private theorem jump944 :
    Decode.isValidJumpDest submissionBytecode 944 = true :=
  Artifact.isValidJumpDest_index 717 (by rfl)

def gasSteps_finish (entry : State) (accumulator : UInt256)
    (count baseSize e m baseOff direct : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256) (hdirect : direct ≤ baseSize)
    (hcode : entry.executionEnv.code = submissionBytecode)
    (hfork : entry.fork = .Osaka) (hrun : entry.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig entry.executionEnv.precompileConfig
      entry.executionEnv.fork entry.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loopState entry accumulator count baseSize baseOff direct
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)
        (baseSize - direct))
      (initialAccumulator entry accumulator count baseSize baseOff direct
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)) := by
  let progress := baseProgressFrom count baseOff direct (baseSize - direct) entry
  let fullRest := [UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff] ++ rest
  let helperRest := [accumulator, UInt256.ofNat count,
    UInt256.ofNat baseSize] ++ fullRest
  have hhelper : helperRest.length < 1000 := by
    simp [helperRest, fullRest]
    omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerGuardPath
      (by simpa [outerLoop, progress, Artifact.submissionArtifact] using hcode)
      (by simpa [outerLoop, progress, State.fork] using hfork)
      (run_outerFinishGuard progress accumulator count baseSize fullRest
        (by simp [fullRest]; omega) hbase
        (by simpa [progress] using hcode) (by simpa [progress] using hrun))
      (by simpa [outerLoop, progress] using hrun)
      (by simpa [outerLoop, progress, State.fork] using hnp)
  have htoAccumulator := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerFinishToAccumulatorPath
      (by simpa [outerExit, outerLoop, progress,
        Artifact.submissionArtifact] using hcode)
      (by simpa [outerExit, outerLoop, progress, State.fork] using hfork)
      (run_outerFinishToAccumulator progress accumulator count baseSize
        baseSize fullRest
        (by simp [fullRest]; omega) (by simpa [progress] using hcode)
        (by simpa [progress] using hrun))
      (by simpa [outerExit, outerLoop, progress] using hrun)
      (by simpa [outerExit, outerLoop, progress, State.fork] using hnp)
  have hadd := BigHelpers.gasSteps_addMaskedMod
    (convertedExit entry accumulator count baseSize baseOff direct fullRest)
    2048 3072 1 0 count 944 helperRest hhelper hcount
    (by simpa [convertedExit, outerExit, outerLoop, progress] using hcode)
    (by simpa [convertedExit, outerExit, outerLoop, progress, State.fork]
      using hfork)
    (by simpa [convertedExit, outerExit, outerLoop, progress] using hrun)
    (by simpa [convertedExit, outerExit, outerLoop, progress, State.fork]
      using hnp)
    jump944
  have hidx : direct + (baseSize - direct) = baseSize := by omega
  exact Challenge.EvmProof.GasSteps.cast
    (hguard.trans (htoAccumulator.trans hadd))
    (by simp [loopState, progress, fullRest, hidx])
    (by simp [initialAccumulator, convertedExit, helperRest, fullRest, progress])

def gasSteps_conversion (entry : State) (accumulator : UInt256)
    (count baseSize e m baseOff direct : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256) (hdirect : direct ≤ baseSize)
    (hoff : baseOff + baseSize < 2 ^ 256)
    (hcode : entry.executionEnv.code = submissionBytecode)
    (hfork : entry.fork = .Osaka) (hrun : entry.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig entry.executionEnv.precompileConfig
      entry.executionEnv.fork entry.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loopState entry accumulator count baseSize baseOff direct
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) 0)
      (initialAccumulator entry accumulator count baseSize baseOff direct
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)) :=
  (gasSteps_loop entry accumulator count baseSize e m baseOff direct rest hcap
    hcount hbase hdirect hoff hcode hfork hrun hnp).trans
  (gasSteps_finish entry accumulator count baseSize e m baseOff direct rest hcap
    hcount hbase hdirect hcode hfork hrun hnp)

/-- The loaded-prefix state is exactly the loop head at index `direct`. -/
theorem loopState_zero (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256) :
    loopState (baseLoopEntry s accumulator count baseSize e m baseOff rest)
        accumulator count baseSize baseOff
        (basePrefix s accumulator count baseSize
          (baseTail baseSize e m baseOff rest))
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) 0 =
      baseLoopEntry s accumulator count baseSize e m baseOff rest := by
  simp [loopState, baseProgressFrom, outerLoop, baseLoopEntry,
    BigLoad.loadReturned, BigLoad.loadLoop, frame, baseTail, basePrefix]

def gasSteps_baseConversion (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 990)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcount : count < 2 ^ 256) (hbase : baseSize < 2 ^ 256)
    (hoff : baseOff < 2 ^ 256) (hoffFit : baseOff + baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (BigModulus.scanNonzero s count (baseTail baseSize e m baseOff rest))
      (initialAccumulator
        (baseLoopEntry s accumulator count baseSize e m baseOff rest)
        accumulator count baseSize baseOff
        (basePrefix s accumulator count baseSize
          (baseTail baseSize e m baseOff rest))
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)) := by
  have hsetup := gasSteps_baseSetup s accumulator count baseSize e m baseOff rest
    hcap hacc hcount hbase hoff (by omega) hcode hfork hrun hnp
  have hentryCode :
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).executionEnv.code
        = submissionBytecode := by
    simpa [baseLoopEntry, BigLoad.loadReturned, BigLoad.loadLoop, baseDirectOf,
      baseWritten, afterClearDouble, BigHelpers.clearReturned, stubbed,
      BigModulus.scanNonzero] using hcode
  have hentryFork :
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).fork
        = .Osaka := by
    simpa [baseLoopEntry, BigLoad.loadReturned, BigLoad.loadLoop, baseDirectOf,
      baseWritten, afterClearDouble, BigHelpers.clearReturned, stubbed,
      BigModulus.scanNonzero, State.fork] using hfork
  have hentryRun :
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).halt
        = .Running := by
    simpa [baseLoopEntry, BigLoad.loadReturned, BigLoad.loadLoop, baseDirectOf,
      baseWritten, afterClearDouble, BigHelpers.clearReturned, stubbed,
      BigModulus.scanNonzero] using hrun
  have hentryNp : Precompile.isPrecompileWithConfig
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).executionEnv.precompileConfig
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).executionEnv.fork
      (baseLoopEntry s accumulator count baseSize e m baseOff rest).executionEnv.codeAddr
      = false := by
    simpa [baseLoopEntry, BigLoad.loadReturned, BigLoad.loadLoop, baseDirectOf,
      baseWritten, afterClearDouble, BigHelpers.clearReturned, stubbed,
      BigModulus.scanNonzero, State.fork] using hnp
  have hconv := gasSteps_conversion
    (baseLoopEntry s accumulator count baseSize e m baseOff rest) accumulator
    count baseSize e m baseOff
    (basePrefix s accumulator count baseSize
      (baseTail baseSize e m baseOff rest)) rest hcap hcount hbase
    (directValue_le _ count baseSize) hoffFit hentryCode hentryFork hentryRun
    hentryNp
  exact hsetup.trans (Challenge.EvmProof.GasSteps.cast hconv
    (loopState_zero s accumulator count baseSize e m baseOff rest) rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseLoop
