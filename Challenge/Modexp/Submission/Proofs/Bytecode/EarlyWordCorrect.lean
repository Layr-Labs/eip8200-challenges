import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactEarlyWordPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordGas
import Challenge.Modexp.Submission.Proofs.Bytecode.MainGas
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas
import Challenge.Modexp.Submission.Proofs.PrimeCertificates

set_option warningAsError true

/-!
# Total initial dispatch through the early one-word wrapper

The initial hop always reaches pc 5224. Matching headers enter the existing
Fermat/window proof at pc 4885. Every other header restores the exact legacy
entry at pc 1314 with an empty stack and unchanged memory and environment.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordCorrect

open EvmSemantics EvmSemantics.EVM
open WindowTwentyOneBinding WindowTwentyOnePositive EarlyWordProgram

abbrev Handled (input : ByteArray) : Prop :=
  ∃ final : State,
    Nonempty (Challenge.EvmProof.GasSteps
      (initialState submissionBytecode input 0) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input)

private def environment (input : ByteArray) :
    Environment Artifact.submissionArtifact .Osaka
      (initialState submissionBytecode input 0) where
  sizeBound := by
    change submissionBytecode.size < 2 ^ 256
    rw [submissionBytecode_size]
    norm_num
  code := rfl
  forkEq := rfl
  running := rfl
  noPrecompile := deployAddress_not_precompile

/-- Every non-matching header that is not a small-exponent hit reaches the
unchanged legacy entry exactly. -/
def legacy (input : ByteArray) (hmiss : ¬ WindowTwentyOneInput.Matches input)
    (hsmall : ¬ EarlyWordSmallExp.SmallExpGuard input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (Main.trampolineState input 1233) := by
  have tail := (EarlyWordGas.steps_toSmallExp Artifact.earlyWordPaths
    (initialState submissionBytecode input 0) (environment input) input rfl
    hmiss).trans
    (EarlyWordGas.steps_smallExp_bail Artifact.earlyWordPaths
      Artifact.earlyWordSmallExpPaths
      (initialState submissionBytecode input 0) (environment input) input rfl
      hsmall)
  change Challenge.EvmProof.GasSteps (Main.trampolineState input 5256)
    (Main.trampolineState input 1233) at tail
  exact (Main.gasSteps_entryHop input).trans tail

/-- A small-exponent hit returns the decided word directly. -/
def smallExp (input : ByteArray)
    (hmiss : ¬ WindowTwentyOneInput.Matches input)
    (hsmall : EarlyWordSmallExp.SmallExpGuard input) :
    Handled input := by
  have hfront := (EarlyWordGas.steps_toSmallExp Artifact.earlyWordPaths
    (initialState submissionBytecode input 0) (environment input) input rfl
    hmiss).trans
    (EarlyWordGas.steps_smallExp_hit Artifact.earlyWordPaths
      Artifact.earlyWordSmallExpPaths
      (initialState submissionBytecode input 0) (environment input) input rfl
      rfl hsmall)
  change Challenge.EvmProof.GasSteps (Main.trampolineState input 5256)
    (EarlyWordSmallExp.smallExpFinal
      (initialState submissionBytecode input 0) input 0
      (EarlyWordProgram.headerStack input)) at hfront
  refine ⟨_, ⟨(Main.gasSteps_entryHop input).trans hfront⟩,
    EarlyWordSmallExp.smallExpFinal_isDone _ _ _ _ rfl,
    EarlyWordSmallExp.smallExpFinal_result _ _ _ _ hsmall⟩

/-- Every matching header has a complete initial-state correctness trace. -/
def hit (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    Handled input := by
  obtain ⟨final, ⟨tail⟩, done, result⟩ := FermatGas.handled
    Artifact.fermatPaths Artifact.twentyOnePaths
    (initialState submissionBytecode input 0) (environment input) rfl input hmatch
    (by exact PrimeCertificates.bn254P_prime) (by exact PrimeCertificates.secpP_prime)
  have entrySteps := EarlyWordGas.steps_hit Artifact.earlyWordPaths
    (initialState submissionBytecode input 0) (environment input) input rfl hmatch
  change Challenge.EvmProof.GasSteps (Main.trampolineState input 5256)
    (state (initialState submissionBytecode input 0) input (UInt256.ofNat 4888)) at entrySteps
  exact ⟨final, ⟨(Main.gasSteps_entryHop input).trans (entrySteps.trans tail)⟩,
    done, result⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordCorrect
