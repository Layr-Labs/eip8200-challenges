import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram

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
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2302 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 1684 15 2302 WindowTwentyOneEntry.widthProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_miss :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2321 WindowTwentyOneEntry.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 1699 2 2321 WindowTwentyOneEntry.missProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2325 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 1701 1 2325 WindowTwentyOneEntry.baseProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2326 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 1702 4 2326 WindowTwentyOneEntry.modulusProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2332 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1706 8 2332 WindowTwentyOneEntry.normalizeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2342 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 1714 92 2342 WindowTwentyOneTableBuild.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_init :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2435 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 1806 16 2435 WindowTwentyOneInit.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_entry :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2479 WindowTwentyOneLoop.entryProgram :=
  WindowTwentyOneSlice.block allWellFormed 1822 0 2479 WindowTwentyOneLoop.entryProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_trampoline :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2479 WindowTwentyOneLoop.trampolineProgram :=
  WindowTwentyOneSlice.block allWellFormed 1822 16 2479 WindowTwentyOneLoop.trampolineProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_body :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2501 WindowTwentyOneLoop.bodyProgram :=
  WindowTwentyOneSlice.block allWellFormed 1838 411 2501 WindowTwentyOneLoop.bodyProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2958 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 2249 5 2958 WindowTwentyOneReturn.program
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_zeroReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2964 WindowTwentyOneReturn.zeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 2254 7 2964 WindowTwentyOneReturn.zeroProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 43 FermatProgram.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 32 14 43 FermatProgram.primeProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_exponent :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 96 FermatProgram.exponentProgram :=
  WindowTwentyOneSlice.block allWellFormed 46 9 96 FermatProgram.exponentProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_result :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 108 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 55 16 108 FermatProgram.returnProgram
    (by decide) (by rfl)
    (by rw [locations_map_instruction]; rfl) (by decide)

def fermatPaths : FermatProgram.Paths submissionArtifact .Osaka where
  prime := fermat_prime
  exponent := fermat_exponent
  result := fermat_result
  legacyJump := by exact isValidJumpDest_index 1701 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths submissionArtifact .Osaka where
  width := nine_width
  miss := nine_miss
  base := nine_base
  modulus := nine_modulus
  normalize := nine_normalize
  table := nine_table
  init := nine_init
  entry := nine_entry
  trampoline := nine_trampoline
  body := nine_body
  finish := nine_finish
  zeroReturn := nine_zeroReturn
  hitJump := by
    have h := isValidJumpDest_index 32 (by rfl)
    exact h
  zeroJump := by
    have h := isValidJumpDest_index 2254 (by rfl)
    exact h
  trampJump := by
    have h := isValidJumpDest_index 1822 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 472 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
