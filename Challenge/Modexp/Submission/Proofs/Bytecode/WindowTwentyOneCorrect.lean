import Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas
import Challenge.Modexp.Submission.Proofs.PrimeCertificates

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect

open EvmSemantics EvmSemantics.EVM
open WindowTwentyOneBinding WindowTwentyOnePositive

private def environment (input : ByteArray) :
    Environment Artifact.submissionArtifact .Osaka (Main.headerState input) where
  sizeBound := by
    change submissionBytecode.size < 2 ^ 256
    rw [submissionBytecode_size]
    norm_num
  code := rfl
  forkEq := rfl
  running := rfl
  noPrecompile := deployAddress_not_precompile

private theorem entry_eq (input : ByteArray) :
    state (Main.headerState input) input (UInt256.ofNat 2633) =
      Dispatch.wordRouteEntryState input := by
  rfl

private theorem miss_eq (input : ByteArray) :
    state (Main.headerState input) input (UInt256.ofNat 517) =
      Dispatch.wordEntryState input := by
  rfl

def handled (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    WindowRoute.Handled input := by
  obtain ⟨final, ⟨trace⟩, done, result⟩ := FermatGas.handled
    Artifact.fermatPaths Artifact.twentyOnePaths (Main.headerState input) (environment input) rfl input hmatch
    (by exact PrimeCertificates.bn254P_prime) (by exact PrimeCertificates.secpP_prime)
  have guard := WindowTwentyOneGasRoute.steps_hit Artifact.twentyOnePaths
    (Main.headerState input) (environment input) input hmatch
  refine ⟨final, ⟨?_⟩, done, result⟩
  change Challenge.EvmProof.GasSteps (Dispatch.wordRouteEntryState input) final
  rw [← entry_eq]
  exact guard.trans trace

def route : WindowRoute.Route where
  enter := Dispatch.gasSteps_wordRouteEnter
  miss := fun input _ _ _ hmiss => by
    have h := WindowTwentyOneGasRoute.steps_miss Artifact.twentyOnePaths
      (Main.headerState input) (environment input) input hmiss
    simpa only [entry_eq, miss_eq] using h
  hit := fun input _ _ _ hmatch => handled input hmatch

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect
