import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FermatNext

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace CycleSubmission.Global.Paths
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

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
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 745 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 521 1 745 WindowTwentyOneEntry.baseProgram
    (by exact Nat.le_trans (by decide : 521 + 1 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 746 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 522 2 746 WindowTwentyOneEntry.modulusProgram
    (by exact Nat.le_trans (by decide : 522 + 2 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 748 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 524 88 748 WindowTwentyOneTableBuild.program
    (by exact Nat.le_trans (by decide : 524 + 88 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_setup :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 837 WindowPrecopyRoute.setupProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 612 3 837 WindowPrecopyRoute.setupProgram
    (by exact Nat.le_trans (by decide : 612 + 3 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_copy :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 841 WindowPrecopyRoute.copyProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 615 7 841 WindowPrecopyRoute.copyProgram
    (by exact Nat.le_trans (by decide : 615 + 7 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_pool :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 849 WindowPrecopyRoute.poolProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 622 314 849 WindowPrecopyRoute.poolProgram
    (by exact Nat.le_trans (by decide : 622 + 314 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_first :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 1163 WindowPrecopyRoute.firstProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 936 5 1163 WindowPrecopyRoute.firstProgram
    (by exact Nat.le_trans (by decide : 936 + 5 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_head :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 1172 (WindowPrecopyRoute.routeWindows 0 60) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 941 840 1172 (WindowPrecopyRoute.routeWindows 0 60)
    (by exact Nat.le_trans (by decide : 941 + 840 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_tail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 2252 WindowPrecopyRoute.tailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1781 49 2252 WindowPrecopyRoute.tailProgram
    (by exact Nat.le_trans (by decide : 1781 + 49 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_fast :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 24 FermatNext.fastProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 17 6 24 FermatNext.fastProgram
    (by exact Nat.le_trans (by decide : 17 + 6 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_join :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 33 FermatNext.joinProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 23 9 33 FermatNext.joinProgram
    (by exact Nat.le_trans (by decide : 23 + 9 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 45 FermatNext.primeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 32 10 45 FermatNext.primeProgram
    (by exact Nat.le_trans (by decide : 32 + 10 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4848 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3889 9 4848 FermatProgram.returnProgram
    (by exact Nat.le_trans (by decide : 3889 + 9 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genCheck :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 101 FermatNext.genCheckProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 47 9 101 FermatNext.genCheckProgram
    (by exact Nat.le_trans (by decide : 47 + 9 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genLoad :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 112 FermatNext.genLoadProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 56 18 112 FermatNext.genLoadProgram
    (by exact Nat.le_trans (by decide : 56 + 18 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_jumpTail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 94 FermatNext.jumpTailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 42 2 94 FermatNext.jumpTailProgram
    (by exact Nat.le_trans (by decide : 42 + 2 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_tail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4839 FermatNext.tailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3882 7 4839 FermatNext.tailProgram
    (by exact Nat.le_trans (by decide : 3882 + 7 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_inverseGuard :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4857 FermatNext.inverseGuardProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3898 6 4857 FermatNext.inverseGuardProgram
    (by exact Nat.le_trans (by decide : 3898 + 6 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_inverse :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4897 HistoricalSearch.FixedExponentProgram.program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3904 1007 4897 HistoricalSearch.FixedExponentProgram.program
    (by exact Nat.le_trans (by decide : 3904 + 1007 ≤ 9188) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

def fermatPaths : FermatNext.Paths CycleSubmission.Artifact.artifact .Osaka where
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
  routeJump := by exact CycleSubmission.Global.Binding.jumpDest 521 (by rfl)
  joinJump := by exact CycleSubmission.Global.Binding.jumpDest 23 (by rfl)
  tailJump := by exact CycleSubmission.Global.Binding.jumpDest 3882 (by rfl)
  inverseJump := by exact CycleSubmission.Global.Binding.jumpDest 3898 (by rfl)
  bigJump := by exact CycleSubmission.Global.Binding.jumpDest 146 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths CycleSubmission.Artifact.artifact .Osaka where
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
    have h := CycleSubmission.Global.Binding.jumpDest 47 (by rfl)
    exact h
  missJump := by
    have h := CycleSubmission.Global.Binding.jumpDest 75 (by rfl)
    exact h

end CycleSubmission.Global.Paths
