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

/-- Instruction-index anchors: the only places the concrete instruction prefix is
assembled.  Each is chained from the previous one, so the assembled slice stays short. -/
private def nine_width :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 843 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 602 14 843 WindowTwentyOneEntry.widthProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_hitTail :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 861 WindowTwentyOneEntry.hitTailProgram :=
  WindowTwentyOneSlice.block allWellFormed 616 4 861 WindowTwentyOneEntry.hitTailProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 872 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 624 1 872 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 873 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 625 2 873 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 876 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 627 3 876 WindowTwentyOneEntry.normalizeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 879 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 630 88 879 WindowTwentyOneTableBuild.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_setup :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 968 WindowPrecopyRoute.setupProgram :=
  WindowTwentyOneSlice.block allWellFormed 718 6 968 WindowPrecopyRoute.setupProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_copy :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 976 WindowPrecopyRoute.copyProgram :=
  WindowTwentyOneSlice.block allWellFormed 724 5 976 WindowPrecopyRoute.copyProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_pool :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 981 WindowPrecopyRoute.poolProgram :=
  WindowTwentyOneSlice.block allWellFormed 729 315 981 WindowPrecopyRoute.poolProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_first :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1296 WindowPrecopyRoute.firstProgram :=
  WindowTwentyOneSlice.block allWellFormed 1044 7 1296 WindowPrecopyRoute.firstProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_head :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1308 (WindowPrecopyRoute.routeWindows 0 60) :=
  WindowTwentyOneSlice.block allWellFormed 1051 840 1308 (WindowPrecopyRoute.routeWindows 0 60)
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_jump :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2388 WindowPrecopyRoute.jumpProgram :=
  WindowTwentyOneSlice.block allWellFormed 1891 2 2388 WindowPrecopyRoute.jumpProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_tail :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 5483 WindowPrecopyRoute.tailProgram :=
  WindowTwentyOneSlice.block allWellFormed 4312 49 5483 WindowPrecopyRoute.tailProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_fast :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 24 FermatNext.fastProgram :=
  WindowTwentyOneSlice.block allWellFormed 17 5 24 FermatNext.fastProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_join :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 31 FermatNext.joinProgram :=
  WindowTwentyOneSlice.block allWellFormed 22 7 31 FermatNext.joinProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 40 FermatNext.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 29 11 40 FermatNext.primeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 90 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 40 12 90 FermatProgram.returnProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genCheck :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 103 FermatNext.genCheckProgram :=
  WindowTwentyOneSlice.block allWellFormed 52 9 103 FermatNext.genCheckProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_genLoad :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 114 FermatNext.genLoadProgram :=
  WindowTwentyOneSlice.block allWellFormed 61 15 114 FermatNext.genLoadProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

def fermatPaths : FermatNext.Paths submissionArtifact .Osaka where
  fast := fermat_fast
  join := fermat_join
  prime := fermat_prime
  result := fermat_result
  genCheck := fermat_genCheck
  genLoad := fermat_genLoad
  routeJump := by exact isValidJumpDest_index 624 (by rfl)
  joinJump := by exact isValidJumpDest_index 22 (by rfl)
  bigJump := by exact isValidJumpDest_index 165 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths submissionArtifact .Osaka where
  width := nine_width
  hitTail := nine_hitTail
  base := nine_base
  modulus := nine_modulus
  normalize := nine_normalize
  table := nine_table
  setup := nine_setup
  copy := nine_copy
  pool := nine_pool
  first := nine_first
  head := nine_head
  jump := nine_jump
  tail := nine_tail
  tailJump := by exact isValidJumpDest_index 4312 (by rfl)
  genJump := by
    have h := isValidJumpDest_index 52 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 78 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
