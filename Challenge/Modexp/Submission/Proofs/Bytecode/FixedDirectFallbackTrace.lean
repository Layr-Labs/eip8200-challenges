import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectValueTrace
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectFallbackCore

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Generic fallback from the fixed-exponent dispatcher

Every nonmatching exponent copies `R1` to `ACC` and rejoins the unchanged
generic exponent loop at its exact entry state.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectFallbackTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectFallbackCore
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

set_option linter.unusedSimpArgs false in
theorem run_fallback (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.fallback
      (FixedDirectStates.fallback s memory n bsize esize msize) =
      some (missState s memory n bsize esize msize) := by
  rw [show Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.fallback
      (FixedDirectStates.fallback s memory n bsize esize msize) =
      runInstructions fallbackProgram
        (FixedDirectStates.fallback s memory n bsize esize msize) by
    simp (config := { maxSteps := 300000 })
      [FixedDirectPaths.fallback, fallbackProgram, runInstructions,
        opAt, pushAt, wfOp,
        Challenge.EvmProof.Stepper.runLocatedBlock,
        Challenge.EvmProof.Stepper.runLocated,
        Challenge.EvmProof.Stepper.runInstr,
        FixedDirectStates.fallback, Exp.outer, hcode, hrun,
        jumpDest1703,
        Challenge.EvmProof.Word.literal_eq_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.succ_ofNat_mod,
        Challenge.EvmProof.Word.ofNat_add_mod]]
  exact run_fallbackProgram s memory n bsize esize msize hn hn32 hactive
    (by simpa [hcode] using jumpDest1703) hrun

def gasSteps_fallback (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hactive : 298 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.fallback s memory n bsize esize msize)
      (missState s memory n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka FixedDirectPaths.fallback
    (by simpa [FixedDirectStates.fallback, Artifact.submissionArtifact] using hcode)
    (by simpa [FixedDirectStates.fallback] using hfork)
    (run_fallback s memory n bsize esize msize hn hn32 hactive hcode hrun)
    (by simpa [FixedDirectStates.fallback] using hrun)
    (by simpa [FixedDirectStates.fallback] using hnp)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectFallbackTrace
