import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedBoundarySites

set_option warningAsError true
set_option autoImplicit false

/-!
# Local-cap EVM certificates for exact packed round sites

`PackedRoundSites` supplies the exact artifact path for every emitted round.
This module applies the generic run-op bridge to one selected round.  The
abstract evaluator result is an explicit premise so arithmetic and artifact
correspondence remain separate and neither is assumed from the other.

The theorem is intentionally local: its budget is the entry stack plus the
selected round only.  Whole-compression assembly must instantiate it eighty
times, insert `PackedBoundarySites.boundary_certificate` at four group seams,
and compose the resulting `GasSteps` values.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedRoundCertificate

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRunOpBridge
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRoundSites

/-- A single emitted round, tied to its exact final-artifact slice and lifted
to an actual gas-parametric EVM trace. -/
theorem round_certificate (round : Fin 80) (s : State)
    (out : List UInt256)
    (hbudget : s.stack.length +
      (emitRound (phaseAt round.val) round.val).length < 1024)
    (hstart : PathStarts (roundSite round).path s)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (habstract : runOps (memoryWord s)
      (emitRound (phaseAt round.val) round.val) s.stack = some out) :
    ∃ t, Stepper.runLocatedBlock (roundSite round).path s = some t ∧
      ∃ _trace : GasSteps s t, t.stack = out ∧ t.memory = s.memory := by
  exact roundsCertificate (round_straightLine round) hbudget hstart
    hcode hfork hrun hnp habstract

#print axioms round_certificate

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedRoundCertificate
