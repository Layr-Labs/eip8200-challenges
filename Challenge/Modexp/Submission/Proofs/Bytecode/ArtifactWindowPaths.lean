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
each `k`; on a 3,984-instruction list that is `O(start)` work per instruction, and the two
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
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 1372 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 951 14 1372 WindowTwentyOneEntry.widthProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_hitTail :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1390 WindowTwentyOneEntry.hitTailProgram :=
  WindowTwentyOneSlice.block allWellFormed 965 4 1390 WindowTwentyOneEntry.hitTailProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_adapter :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 116 WindowTwentyOneEntry.adapterProgram :=
  WindowTwentyOneSlice.block allWellFormed 62 10 116 WindowTwentyOneEntry.adapterProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1395 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 969 1 1395 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 1396 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 970 2 1396 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1399 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 972 7 1399 WindowTwentyOneEntry.normalizeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 1408 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 979 92 1408 WindowTwentyOneTableBuild.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_init :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 1503 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 1071 11 1503 WindowTwentyOneInit.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_entry :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1519 WindowTwentyOneLoop.entryProgram :=
  WindowTwentyOneSlice.block allWellFormed 1082 0 1519 WindowTwentyOneLoop.entryProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_trampoline :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1519 WindowTwentyOneLoop.trampolineProgram :=
  WindowTwentyOneSlice.block allWellFormed 1082 14 1519 WindowTwentyOneLoop.trampolineProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_body :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1538 WindowTwentyOneLoop.bodyProgram :=
  WindowTwentyOneSlice.block allWellFormed 1096 411 1538 WindowTwentyOneLoop.bodyProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1995 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 1507 5 1995 WindowTwentyOneReturn.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_entry :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 25 FermatNext.entryProgram :=
  WindowTwentyOneSlice.block allWellFormed 19 16 25 FermatNext.entryProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 45 FermatNext.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 35 11 45 FermatNext.primeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 96 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 46 16 96 FermatProgram.returnProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

def fermatPaths : FermatNext.Paths submissionArtifact .Osaka where
  entry := fermat_entry
  prime := fermat_prime
  result := fermat_result
  legacyJump := by exact isValidJumpDest_index 969 (by rfl)

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
  body := nine_body
  finish := nine_finish
  adapterJump := by
    have h := isValidJumpDest_index 62 (by rfl)
    exact h
  entryJump := by
    have h := isValidJumpDest_index 19 (by rfl)
    exact h
  trampJump := by
    have h := isValidJumpDest_index 1082 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 78 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
