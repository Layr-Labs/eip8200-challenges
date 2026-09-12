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
private theorem pcA1612 : Artifact.submissionArtifact.instructionPC 1687 = 2310 := by rfl

private theorem pcA1627 : Artifact.submissionArtifact.instructionPC 1702 = 2330 := by
  rw [show (1702 : Nat) = 1687 + 15 from rfl, instructionPC_add, pcA1612]; rfl

private theorem pcA1629 : Artifact.submissionArtifact.instructionPC 1704 = 2334 := by
  rw [show (1704 : Nat) = 1702 + 2 from rfl, instructionPC_add, pcA1627]; rfl

private theorem pcA1631 : Artifact.submissionArtifact.instructionPC 1706 = 2336 := by
  rw [show (1706 : Nat) = 1704 + 2 from rfl, instructionPC_add, pcA1629]; rfl

private theorem pcA1637 : Artifact.submissionArtifact.instructionPC 1712 = 2344 := by
  rw [show (1712 : Nat) = 1706 + 6 from rfl, instructionPC_add, pcA1631]; rfl

private theorem pcA1645 : Artifact.submissionArtifact.instructionPC 1720 = 2354 := by
  rw [show (1720 : Nat) = 1712 + 8 from rfl, instructionPC_add, pcA1637]; rfl

private theorem pcA1737 : Artifact.submissionArtifact.instructionPC 1812 = 2470 := by
  rw [show (1812 : Nat) = 1720 + 92 from rfl, instructionPC_add, pcA1645]; rfl

private theorem pcA1755 : Artifact.submissionArtifact.instructionPC 1830 = 2495 := by
  rw [show (1830 : Nat) = 1812 + 18 from rfl, instructionPC_add, pcA1737]; rfl

private theorem pcA2193 : Artifact.submissionArtifact.instructionPC 2268 = 2958 := by rfl

private theorem pcA2198 : Artifact.submissionArtifact.instructionPC 2273 = 2964 := by
  rw [show (2273 : Nat) = 2268 + 5 from rfl, instructionPC_add, pcA2193]; rfl

private theorem pcA3688 : Artifact.submissionArtifact.instructionPC 32 = 43 := by rfl

private theorem pcA3702 : Artifact.submissionArtifact.instructionPC 46 = 96 := by
  rw [show (46 : Nat) = 32 + 14 from rfl, instructionPC_add, pcA3688]; rfl

private theorem pcA3711 : Artifact.submissionArtifact.instructionPC 55 = 108 := by
  rw [show (55 : Nat) = 46 + 9 from rfl, instructionPC_add, pcA3702]; rfl


private def nine_width :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2310 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 1687 15 2310 WindowTwentyOneEntry.widthProgram
    (by decide) pcA1612
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_miss :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2330 WindowTwentyOneEntry.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 1702 2 2330 WindowTwentyOneEntry.missProgram
    (by decide) pcA1627
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2334 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 1704 2 2334 WindowTwentyOneEntry.baseProgram
    (by decide) pcA1629
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2336 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 1706 6 2336 WindowTwentyOneEntry.modulusProgram
    (by decide) pcA1631
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2344 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1712 8 2344 WindowTwentyOneEntry.normalizeProgram
    (by decide) pcA1637
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2354 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 1720 92 2354 WindowTwentyOneTableBuild.program
    (by decide) pcA1645
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_init :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2470 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 1812 18 2470 WindowTwentyOneInit.program
    (by decide) pcA1737
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_iteration :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2495 WindowTwentyOneLoop.iterationProgram :=
  WindowTwentyOneSlice.block allWellFormed 1830 438 2495 WindowTwentyOneLoop.iterationProgram
    (by decide) pcA1755
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2958 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 2268 5 2958 WindowTwentyOneReturn.program
    (by decide) pcA2193
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_zeroReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2964 WindowTwentyOneReturn.zeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 2273 7 2964 WindowTwentyOneReturn.zeroProgram
    (by decide) pcA2198
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime : WindowTwentyOneBinding.Block submissionArtifact .Osaka 43 FermatProgram.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 32 14 43 FermatProgram.primeProgram (by decide) pcA3688
    (by rw [locations_map_instruction]; rfl) (by decide)
private def fermat_exponent : WindowTwentyOneBinding.Block submissionArtifact .Osaka 96 FermatProgram.exponentProgram :=
  WindowTwentyOneSlice.block allWellFormed 46 9 96 FermatProgram.exponentProgram (by decide) pcA3702
    (by rw [locations_map_instruction]; rfl) (by decide)
private def fermat_result : WindowTwentyOneBinding.Block submissionArtifact .Osaka 108 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 55 16 108 FermatProgram.returnProgram (by decide) pcA3711
    (by rw [locations_map_instruction]; rfl) (by decide)
def fermatPaths : FermatProgram.Paths submissionArtifact .Osaka where
  prime := fermat_prime
  exponent := fermat_exponent
  result := fermat_result
  legacyJump := by exact isValidJumpDest_index 1704 (by rfl)

def twentyOnePaths : WindowTwentyOneGasRoute.Paths submissionArtifact .Osaka where
  width := nine_width
  miss := nine_miss
  base := nine_base
  modulus := nine_modulus
  normalize := nine_normalize
  table := nine_table
  init := nine_init
  iteration := nine_iteration
  finish := nine_finish
  zeroReturn := nine_zeroReturn
  hitJump := by
    have h := isValidJumpDest_index 32 (by rfl)
    exact h
  zeroJump := by
    have h := isValidJumpDest_index 2273 (by rfl)
    exact h
  loopJump := by
    have h := isValidJumpDest_index 1830 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 472 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
