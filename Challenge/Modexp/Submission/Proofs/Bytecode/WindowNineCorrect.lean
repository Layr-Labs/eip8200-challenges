import Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineCorrect

open EvmSemantics EvmSemantics.EVM
open WindowNineBinding WindowNinePositive

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
    state (Main.headerState input) input (UInt256.ofNat 3013) =
      Dispatch.wordRouteEntryState input := by
  rfl

private theorem miss_eq (input : ByteArray) :
    state (Main.headerState input) input (UInt256.ofNat 517) =
      Dispatch.wordEntryState input := by
  rfl

def handled (input : ByteArray) (hmatch : WindowNineInput.Matches input) :
    WindowRoute.Handled input := by
  obtain ⟨final, ⟨trace⟩, done, result⟩ := WindowNineGasRoute.handled
    Artifact.ninePaths (Main.headerState input) (environment input) rfl input hmatch
  have guard := WindowNineGasRoute.steps_hit Artifact.ninePaths
    (Main.headerState input) (environment input) input hmatch
  refine ⟨final, ⟨?_⟩, done, result⟩
  change Challenge.EvmProof.GasSteps (Dispatch.wordRouteEntryState input) final
  rw [← entry_eq]
  exact guard.trans trace

def route : WindowRoute.Route where
  enter := Dispatch.gasSteps_wordRouteEnter
  miss := fun input _ _ _ hmiss => by
    have h := WindowNineGasRoute.steps_miss Artifact.ninePaths
      (Main.headerState input) (environment input) input hmiss
    simpa only [entry_eq, miss_eq] using h
  hit := fun input _ _ _ hmatch => handled input hmatch

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineCorrect
