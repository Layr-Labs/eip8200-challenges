import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectValueTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Bail from the fixed-exponent dispatcher

Every nonmatching exponent leaves the fast path through the six-word bail
trampoline `BAIL6` (pc 1054) and lands on `modexpBig` (pc 237) with the outer
frame untouched.  The generic exponent loop is no longer reachable from here.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectFallbackTrace

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
open Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
open Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

set_option linter.unusedSimpArgs false in
/-- `bail`: the trampoline the three recogniser misses name.  It is three
data-independent instructions that touch no memory and pop only the target the
`JUMP` itself pushed, so the only field that moves is `pc`. -/
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
      FixedDirectPaths.pcTramp717, FixedDirectPaths.pcTramp718,
      FixedDirectPaths.pcTramp719,
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
