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
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 804 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 568 14 804 WindowTwentyOneEntry.widthProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_hitTail :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 822 WindowTwentyOneEntry.hitTailProgram :=
  WindowTwentyOneSlice.block allWellFormed 582 4 822 WindowTwentyOneEntry.hitTailProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_adapter :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 116 WindowTwentyOneEntry.adapterProgram :=
  WindowTwentyOneSlice.block allWellFormed 62 10 116 WindowTwentyOneEntry.adapterProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 827 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 586 1 827 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 828 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 587 2 828 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 831 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 589 7 831 WindowTwentyOneEntry.normalizeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 840 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 596 91 840 WindowTwentyOneTableBuild.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_init :
  WindowTwentyOneBinding.Block submissionArtifact .Osaka 932 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 687 14 932 WindowTwentyOneInit.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_entry :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 951 WindowTwentyOneLoop.entryProgram :=
  WindowTwentyOneSlice.block allWellFormed 701 0 951 WindowTwentyOneLoop.entryProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_trampoline :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 951 WindowTwentyOneLoop.trampolineProgram :=
  WindowTwentyOneSlice.block allWellFormed 701 14 951 WindowTwentyOneLoop.trampolineProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

/-! The window loop is unrolled in this image: the three passes are three
straight-line regions, not one block reached three times.  Each body is the same
401-instruction program at a different pc, and the two links between consecutive
passes are the same 7-instruction program at a different pc.

Each link is an eighteen-byte dead span followed by the five-instruction staging
head.  The dead span is a single `PUSH16` whose sixteen-byte immediate swallows
the whole span, then `POP`: the two links therefore have the SAME instruction
count now, where they used to differ (17 and 16).  No pc moves -- the span is
still eighteen bytes -- so only the instruction indices below change.

| block | instruction index | count | pc |
|-------|-------------------|-------|----|
| body0 |  728 | 401 |  970 |
| link0 | 1129 |   7 | 1413 |
| body1 | 1136 | 401 | 1436 |
| link1 | 1537 |   7 | 1879 |
| body2 | 1544 | 402 | 1902 | -/

private def nine_body0 :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 970 (WindowTwentyOneLoop.bodyProgram (21 * 0)) :=
  WindowTwentyOneSlice.block allWellFormed 715 401 970 (WindowTwentyOneLoop.bodyProgram (21 * 0))
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_link0 :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1413 WindowTwentyOneLoop.linkProgram :=
  WindowTwentyOneSlice.block allWellFormed 1116 7 1413 WindowTwentyOneLoop.linkProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_body1 :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1436 (WindowTwentyOneLoop.bodyProgram (21 * 1)) :=
  WindowTwentyOneSlice.block allWellFormed 1123 401 1436 (WindowTwentyOneLoop.bodyProgram (21 * 1))
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_link1 :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1879 WindowTwentyOneLoop.linkProgramB :=
  WindowTwentyOneSlice.block allWellFormed 1524 7 1879 WindowTwentyOneLoop.linkProgramB
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_body2 :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 1902 (WindowTwentyOneLoop.bodyProgramLast 42) :=
  WindowTwentyOneSlice.block allWellFormed 1531 402 1902 (WindowTwentyOneLoop.bodyProgramLast 42)
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2345 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 1933 5 2345 WindowTwentyOneReturn.program
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
  legacyJump := by exact isValidJumpDest_index 586 (by rfl)

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
  link0 := nine_link0
  body1 := nine_body1
  link1 := nine_link1
  body2 := nine_body2
  finish := nine_finish
  adapterJump := by
    have h := isValidJumpDest_index 62 (by rfl)
    exact h
  entryJump := by
    have h := isValidJumpDest_index 19 (by rfl)
    exact h
  trampJump := by
    have h := isValidJumpDest_index 701 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 78 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
