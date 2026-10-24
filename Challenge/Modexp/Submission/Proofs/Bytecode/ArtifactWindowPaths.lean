import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext

set_option warningAsError true
set_option maxRecDepth 40000
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
  WindowTwentyOneSlice.block allWellFormed 521 1 745 WindowTwentyOneEntry.baseProgram
    (by exact Nat.le_trans (by decide : 521 + 1 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 746 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 522 2 746 WindowTwentyOneEntry.modulusProgram
    (by exact Nat.le_trans (by decide : 522 + 2 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 748 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 524 88 748 WindowTwentyOneTableBuild.program
    (by exact Nat.le_trans (by decide : 524 + 88 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_setup :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 837 WindowPrecopyRoute.setupProgram :=
  WindowTwentyOneSlice.block allWellFormed 612 3 837 WindowPrecopyRoute.setupProgram
    (by exact Nat.le_trans (by decide : 612 + 3 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_copy :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 841 WindowPrecopyRoute.copyProgram :=
  WindowTwentyOneSlice.block allWellFormed 615 7 841 WindowPrecopyRoute.copyProgram
    (by exact Nat.le_trans (by decide : 615 + 7 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_pool :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 849 WindowPrecopyRoute.poolProgram :=
  WindowTwentyOneSlice.block allWellFormed 622 314 849 WindowPrecopyRoute.poolProgram
    (by exact Nat.le_trans (by decide : 622 + 314 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_first :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1163 WindowPrecopyRoute.firstProgram :=
  WindowTwentyOneSlice.block allWellFormed 936 5 1163 WindowPrecopyRoute.firstProgram
    (by exact Nat.le_trans (by decide : 936 + 5 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_head :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1172 (WindowPrecopyRoute.routeWindows 0 60) :=
  WindowTwentyOneSlice.block allWellFormed 941 840 1172 (WindowPrecopyRoute.routeWindows 0 60)
    (by exact Nat.le_trans (by decide : 941 + 840 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_tail :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2252 WindowPrecopyRoute.tailProgram :=
  WindowTwentyOneSlice.block allWellFormed 1781 49 2252 WindowPrecopyRoute.tailProgram
    (by exact Nat.le_trans (by decide : 1781 + 49 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_fast :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 24 FermatNext.fastProgram :=
  WindowTwentyOneSlice.block allWellFormed 17 6 24 FermatNext.fastProgram
    (by exact Nat.le_trans (by decide : 17 + 6 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_join :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 33 FermatNext.joinProgram :=
  WindowTwentyOneSlice.block allWellFormed 23 9 33 FermatNext.joinProgram
    (by exact Nat.le_trans (by decide : 23 + 9 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 45 FermatNext.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 32 10 45 FermatNext.primeProgram
    (by exact Nat.le_trans (by decide : 32 + 10 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 9808 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 7699 9 9808 FermatProgram.returnProgram
    (by exact Nat.le_trans (by decide : 7699 + 9 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genCheck :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 101 FermatNext.genCheckProgram :=
  WindowTwentyOneSlice.block allWellFormed 47 9 101 FermatNext.genCheckProgram
    (by exact Nat.le_trans (by decide : 47 + 9 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genLoad :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 112 FermatNext.genLoadProgram :=
  WindowTwentyOneSlice.block allWellFormed 56 18 112 FermatNext.genLoadProgram
    (by exact Nat.le_trans (by decide : 56 + 18 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_jumpTail :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 94 FermatNext.jumpTailProgram :=
  WindowTwentyOneSlice.block allWellFormed 42 2 94 FermatNext.jumpTailProgram
    (by exact Nat.le_trans (by decide : 42 + 2 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_tail :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 9799 FermatNext.tailProgram :=
  WindowTwentyOneSlice.block allWellFormed 7692 7 9799 FermatNext.tailProgram
    (by exact Nat.le_trans (by decide : 7692 + 7 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_inverseGuard :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 9817 FermatNext.inverseGuardProgram :=
  WindowTwentyOneSlice.block allWellFormed 7708 6 9817 FermatNext.inverseGuardProgram
    (by exact Nat.le_trans (by decide : 7708 + 6 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_inverse :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 9857 HistoricalSearch.FixedExponentProgram.program :=
  WindowTwentyOneSlice.block allWellFormed 7714 1007 9857 HistoricalSearch.FixedExponentProgram.program
    (by exact Nat.le_trans (by decide : 7714 + 1007 ≤ 8721) (Nat.le_of_eq submissionInstructions_count.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

def fermatPaths : FermatNext.Paths submissionArtifact .Osaka where
  fast := fermat_fast
  join := fermat_join
  prime := fermat_prime
  jumpTail := fermat_jumpTail
  tail := fermat_tail
  inverseGuard := fermat_inverseGuard
  inverse := fermat_inverse
  result := fermat_result
  genCheck := fermat_genCheck
  genLoad := fermat_genLoad
  routeJump := by exact isValidJumpDest_index 521 (by rfl)
  joinJump := by exact isValidJumpDest_index 23 (by rfl)
  tailJump := by exact isValidJumpDest_index 7692 (by rfl)
  inverseJump := by exact isValidJumpDest_index 7708 (by rfl)
  bigJump := by exact isValidJumpDest_index 146 (by rfl)

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
    have h := isValidJumpDest_index 47 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 75 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
