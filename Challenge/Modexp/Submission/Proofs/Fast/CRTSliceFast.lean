import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
set_option warningAsError true
namespace Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

theorem locations_map {artifact : ProgramArtifact} {fork : Fork}
    (cert : AllWellFormed artifact fork) (start count : Nat)
    (bound : start + count ≤ artifact.instructions.length) :
    (locations cert start count bound).map Located.instruction =
      (artifact.instructions.drop start).take count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    rw [List.drop_eq_getElem_cons (show start < artifact.instructions.length by omega)]
    simp only [locations, List.map_cons, List.take_succ_cons, Located.ofIndex]
    congr 1
    exact ih (start + 1) (by omega)

end Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast
