import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectValueTrace

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
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

/-- **S1b.** `bail`: the diverted recogniser miss.  All three recogniser checks
push the trampoline, so this class leaves the fast path here instead of copying
`R1` to `ACC` and rejoining the generic exponent loop.

The block this replaces (`FixedDirectPaths.fallback`, the `MCOPY` rejoin) is gone
from the artifact and its table was already removed; the lemma over it was not
merely stale, it was FALSE -- the miss state is at pc 800 and that block is not
located there. -/
theorem run_bail (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock FixedDirectPaths.bail
      (FixedDirectStates.bailState s memory n bsize esize msize) =
      some (FixedDirectStates.bigCState s memory n bsize esize msize) := by
  simp (config := { maxSteps := 400000 })
    [FixedDirectPaths.bail, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      FixedDirectStates.bailState, FixedDirectStates.bigCState, Exp.outer,
      hcode, hrun,
      FixedDirectPaths.jumpDestBigC,
      FixedDirectPaths.pcTramp578, FixedDirectPaths.pcTramp579,
      FixedDirectPaths.pcTramp580,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod]

def gasSteps_bail (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (FixedDirectStates.bailState s memory n bsize esize msize)
      (FixedDirectStates.bigCState s memory n bsize esize msize) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka FixedDirectPaths.bail
    (by simpa [FixedDirectStates.bailState, Artifact.submissionArtifact] using hcode)
    (by simpa [FixedDirectStates.bailState] using hfork)
    (run_bail s memory n bsize esize msize hcode hrun)
    (by simpa [FixedDirectStates.bailState] using hrun)
    (by simpa [FixedDirectStates.bailState] using hnp)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectFallbackTrace
