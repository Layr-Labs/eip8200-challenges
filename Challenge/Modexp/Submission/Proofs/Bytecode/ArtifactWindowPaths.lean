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
each `k`; on a 4,402-instruction list that is `O(start)` work per instruction, and the two
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

private def nine_adapter :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 112 WindowTwentyOneEntry.adapterProgram :=
  WindowTwentyOneSlice.block allWellFormed 59 12 112 WindowTwentyOneEntry.adapterProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 866 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 620 1 866 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 867 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 621 2 867 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 870 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 623 7 870 WindowTwentyOneEntry.normalizeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 879 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 630 88 879 WindowTwentyOneTableBuild.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_init :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 968 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 718 13 968 WindowTwentyOneInit.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_entry :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 985 WindowTwentyOneLoop.entryProgram :=
  WindowTwentyOneSlice.block allWellFormed 731 0 985 WindowTwentyOneLoop.entryProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_trampoline :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 985 WindowTwentyOneLoop.trampolineProgram :=
  WindowTwentyOneSlice.block allWellFormed 731 8 985 WindowTwentyOneLoop.trampolineProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_body0 :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 994 (WindowTwentyOneLoop.bodyProgram (16 * 0)) :=
  WindowTwentyOneSlice.block allWellFormed 739 309 994 (WindowTwentyOneLoop.bodyProgram (16 * 0))
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_body1 :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1345 (WindowTwentyOneLoop.bodyProgram (16 * 1)) :=
  WindowTwentyOneSlice.block allWellFormed 1048 309 1345 (WindowTwentyOneLoop.bodyProgram (16 * 1))
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_body2 :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1696 (WindowTwentyOneLoop.bodyProgram (16 * 2)) :=
  WindowTwentyOneSlice.block allWellFormed 1357 309 1696 (WindowTwentyOneLoop.bodyProgram (16 * 2))
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_bodyLast :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2047 (WindowTwentyOneLoop.bodyProgramLast 48) :=
  WindowTwentyOneSlice.block allWellFormed 1666 290 2047 (WindowTwentyOneLoop.bodyProgramLast 48)
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2374 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 1956 5 2374 WindowTwentyOneReturn.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_entry :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 22 FermatNext.entryProgram :=
  WindowTwentyOneSlice.block allWellFormed 17 15 22 FermatNext.entryProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 41 FermatNext.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 32 11 41 FermatNext.primeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 92 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 43 16 92 FermatProgram.returnProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

def fermatPaths : FermatNext.Paths submissionArtifact .Osaka where
  entry := fermat_entry
  prime := fermat_prime
  result := fermat_result
  legacyJump := by exact isValidJumpDest_index 620 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths submissionArtifact .Osaka where
  width := nine_width
  hitTail := nine_hitTail
  adapter := nine_adapter
  base := nine_base
  modulus := nine_modulus
  normalize := nine_normalize
  table := nine_table
  init := nine_init
  entry := nine_entry
  trampoline := nine_trampoline
  body0 := nine_body0
  body1 := nine_body1
  body2 := nine_body2
  bodyLast := nine_bodyLast
  finish := nine_finish
  adapterJump := by
    have h := isValidJumpDest_index 59 (by rfl)
    exact h
  entryJump := by
    have h := isValidJumpDest_index 17 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 78 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
