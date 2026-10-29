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
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 517 1 745 WindowTwentyOneEntry.baseProgram
    (by exact Nat.le_trans (by decide : 517+1 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 746 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 518 2 746 WindowTwentyOneEntry.modulusProgram
    (by exact Nat.le_trans (by decide : 518+2 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 748 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 520 88 748 WindowTwentyOneTableBuild.program
    (by exact Nat.le_trans (by decide : 520+88 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_setup :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 837 WindowPrecopyRoute.setupProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 608 3 837 WindowPrecopyRoute.setupProgram
    (by exact Nat.le_trans (by decide : 608+3 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_copy :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 841 WindowPrecopyRoute.copyProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 611 7 841 WindowPrecopyRoute.copyProgram
    (by exact Nat.le_trans (by decide : 611+7 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_pool :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 849 WindowPrecopyRoute.poolProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 618 314 849 WindowPrecopyRoute.poolProgram
    (by exact Nat.le_trans (by decide : 618+314 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_first :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 1163 WindowPrecopyRoute.firstProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 932 5 1163 WindowPrecopyRoute.firstProgram
    (by exact Nat.le_trans (by decide : 932+5 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_head :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 1172 (WindowPrecopyRoute.routeWindows 0 60) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 937 840 1172 (WindowPrecopyRoute.routeWindows 0 60)
    (by exact Nat.le_trans (by decide : 937 + 840 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_tail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 2252 WindowPrecopyRoute.tailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 1777 49 2252 WindowPrecopyRoute.tailProgram
    (by exact Nat.le_trans (by decide : 1777+49 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_fast :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 24 FermatNext.fastProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 17 6 24 FermatNext.fastProgram
    (by exact Nat.le_trans (by decide : 17+6 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_join :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 33 FermatNext.joinProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 23 7 33 FermatNext.joinProgram
    (by exact Nat.le_trans (by decide : 23+7 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 43 FermatNext.primeProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 30 10 43 FermatNext.primeProgram
    (by exact Nat.le_trans (by decide : 30+10 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4848 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3749 9 4848 FermatProgram.returnProgram
    (by exact Nat.le_trans (by decide : 3749+9 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genCheck :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 101 FermatNext.genCheckProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 47 9 101 FermatNext.genCheckProgram
    (by exact Nat.le_trans (by decide : 47+9 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genLoad :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 112 FermatNext.genLoadProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 56 18 112 FermatNext.genLoadProgram
    (by exact Nat.le_trans (by decide : 56+18 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_jumpTail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 92 FermatNext.jumpTailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 40 2 92 FermatNext.jumpTailProgram
    (by exact Nat.le_trans (by decide : 40+2 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_tail :
    WindowTwentyOneBinding.Block CycleSubmission.Artifact.artifact .Osaka 4847 FermatNext.tailProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3748 1 4847 FermatNext.tailProgram
    (by exact Nat.le_trans (by decide : 3748+1 ≤ 8535) (Nat.le_of_eq CycleSubmission.Artifact.instructionCount.symm)) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

def fermatPaths : FermatNext.Paths CycleSubmission.Artifact.artifact .Osaka where
  fast := fermat_fast
  join := fermat_join
  prime := fermat_prime
  jumpTail := fermat_jumpTail
  tail := fermat_tail
  result := fermat_result
  genCheck := fermat_genCheck
  genLoad := fermat_genLoad
  routeJump := by exact CycleSubmission.Global.Binding.jumpDest 517 (by rfl)
  joinJump := by exact CycleSubmission.Global.Binding.jumpDest 23 (by rfl)
  tailJump := by exact CycleSubmission.Global.Binding.jumpDest 3748 (by rfl)
  bigJump := by exact CycleSubmission.Global.Binding.jumpDest 145 (by rfl)

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
