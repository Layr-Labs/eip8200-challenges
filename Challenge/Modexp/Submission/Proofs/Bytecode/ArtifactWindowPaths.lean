import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Artifact

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

/-! ## Artifact-agnostic readings of a certified slice

`WindowTwentyOneSlice.locations` reads its slice as `artifact.instructions[start + k]` for
each `k`; on a 4,360-instruction list that is `O(start)` work per instruction, and the two
`rfl` obligations of `block` pay it twice (elaborator and kernel).  The two lemmas below are
proved for an ARBITRARY `artifact : ProgramArtifact`, so no concrete bytecode enters them;
the concrete submission is then touched once per obligation, and its instruction prefix is
assembled exactly once, at `pcAnchorBlocks`.  Every `Block` statement is unchanged. -/

open Challenge.EvmProof Challenge.EvmProof.Stepper in
/-- A certified consecutive slice reads as one `drop`/`take` of the instruction list. -/
private theorem locations_map_instruction {artifact : ProgramArtifact} {fork : Fork}
    (cert : AllWellFormed artifact fork) (start count : Nat)
    (hbound : start + count ≤ artifact.instructions.length) :
    (WindowTwentyOneSlice.locations cert start count hbound).map Located.instruction =
      (artifact.instructions.drop start).take count := by
  induction count generalizing start with
  | zero => simp [WindowTwentyOneSlice.locations]
  | succ count ih =>
      have hlt : start < artifact.instructions.length := by omega
      rw [WindowTwentyOneSlice.locations, List.map_cons, ih (start + 1) (by omega),
        List.drop_eq_getElem_cons hlt, List.take_succ_cons]
      rfl

/-- `instructionPC` advances by the assembled length of the intervening slice. -/
private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) =
      p.instructionPC base +
        (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 745 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 523 1 745 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 746 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 524 2 746 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 748 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 526 88 748 WindowTwentyOneTableBuild.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_setup :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 837 WindowPrecopyRoute.setupProgram :=
  WindowTwentyOneSlice.block allWellFormed 614 6 837 WindowPrecopyRoute.setupProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_copy :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 845 WindowPrecopyRoute.copyProgram :=
  WindowTwentyOneSlice.block allWellFormed 620 5 845 WindowPrecopyRoute.copyProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_pool :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 850 WindowPrecopyRoute.poolProgram :=
  WindowTwentyOneSlice.block allWellFormed 625 315 850 WindowPrecopyRoute.poolProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_first :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1165 WindowPrecopyRoute.firstProgram :=
  WindowTwentyOneSlice.block allWellFormed 940 7 1165 WindowPrecopyRoute.firstProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_head :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1177 (WindowPrecopyRoute.routeWindows 0 60) :=
  WindowTwentyOneSlice.block allWellFormed 947 840 1177 (WindowPrecopyRoute.routeWindows 0 60)
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_tail :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2257 WindowPrecopyRoute.tailProgram :=
  WindowTwentyOneSlice.block allWellFormed 1787 48 2257 WindowPrecopyRoute.tailProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_fast :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 24 FermatNext.fastProgram :=
  WindowTwentyOneSlice.block allWellFormed 17 6 24 FermatNext.fastProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_join :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 33 FermatNext.joinProgram :=
  WindowTwentyOneSlice.block allWellFormed 23 7 33 FermatNext.joinProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 42 FermatNext.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 30 11 42 FermatNext.primeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 92 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 41 9 92 FermatProgram.returnProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genCheck :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 101 FermatNext.genCheckProgram :=
  WindowTwentyOneSlice.block allWellFormed 50 9 101 FermatNext.genCheckProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genLoad :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 112 FermatNext.genLoadProgram :=
  WindowTwentyOneSlice.block allWellFormed 59 19 112 FermatNext.genLoadProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

def fermatPaths : FermatNext.Paths submissionArtifact .Osaka where
  fast := fermat_fast
  join := fermat_join
  prime := fermat_prime
  result := fermat_result
  genCheck := fermat_genCheck
  genLoad := fermat_genLoad
  routeJump := by exact isValidJumpDest_index 523 (by rfl)
  joinJump := by exact isValidJumpDest_index 23 (by rfl)
  bigJump := by exact isValidJumpDest_index 148 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths submissionArtifact .Osaka where
  base := nine_base
  modulus := nine_modulus
  table := nine_table
  setup := nine_setup
  copy := nine_copy
  pool := nine_pool
  first := nine_first
  head := nine_head
  tail := nine_tail
  genJump := by
    have h := isValidJumpDest_index 50 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 78 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
