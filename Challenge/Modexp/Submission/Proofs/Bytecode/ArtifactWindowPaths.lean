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
private theorem pcA1612 : Artifact.submissionArtifact.instructionPC 1508 = 2042 := by rfl

private theorem pcA1627 : Artifact.submissionArtifact.instructionPC 1523 = 2062 := by
  rw [show (1523 : Nat) = 1508 + 15 from rfl, instructionPC_add, pcA1612]; rfl

private theorem pcA1629 : Artifact.submissionArtifact.instructionPC 1525 = 2066 := by
  rw [show (1525 : Nat) = 1523 + 2 from rfl, instructionPC_add, pcA1627]; rfl

private theorem pcA1631 : Artifact.submissionArtifact.instructionPC 1527 = 2068 := by
  rw [show (1527 : Nat) = 1525 + 2 from rfl, instructionPC_add, pcA1629]; rfl

private theorem pcA1637 : Artifact.submissionArtifact.instructionPC 1533 = 2076 := by
  rw [show (1533 : Nat) = 1527 + 6 from rfl, instructionPC_add, pcA1631]; rfl

private theorem pcA1645 : Artifact.submissionArtifact.instructionPC 1541 = 2086 := by
  rw [show (1541 : Nat) = 1533 + 8 from rfl, instructionPC_add, pcA1637]; rfl

private theorem pcA1737 : Artifact.submissionArtifact.instructionPC 1633 = 2202 := by
  rw [show (1633 : Nat) = 1541 + 92 from rfl, instructionPC_add, pcA1645]; rfl

private theorem pcA1755 : Artifact.submissionArtifact.instructionPC 1651 = 2227 := by
  rw [show (1651 : Nat) = 1633 + 18 from rfl, instructionPC_add, pcA1737]; rfl

private theorem pcA2193 : Artifact.submissionArtifact.instructionPC 2089 = 2690 := by rfl

private theorem pcA2198 : Artifact.submissionArtifact.instructionPC 2094 = 2696 := by
  rw [show (2094 : Nat) = 2089 + 5 from rfl, instructionPC_add, pcA2193]; rfl

private theorem pcA3688 : Artifact.submissionArtifact.instructionPC 3609 = 4752 := by rfl

private theorem pcA3702 : Artifact.submissionArtifact.instructionPC 3623 = 4805 := by
  rw [show (3623 : Nat) = 3609 + 14 from rfl, instructionPC_add, pcA3688]; rfl

private theorem pcA3711 : Artifact.submissionArtifact.instructionPC 3632 = 4817 := by
  rw [show (3632 : Nat) = 3623 + 9 from rfl, instructionPC_add, pcA3702]; rfl


private def nine_width :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2042 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 1508 15 2042 WindowTwentyOneEntry.widthProgram
    (by decide) pcA1612
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_miss :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2062 WindowTwentyOneEntry.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 1523 2 2062 WindowTwentyOneEntry.missProgram
    (by decide) pcA1627
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2066 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 1525 2 2066 WindowTwentyOneEntry.baseProgram
    (by decide) pcA1629
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2068 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 1527 6 2068 WindowTwentyOneEntry.modulusProgram
    (by decide) pcA1631
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2076 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1533 8 2076 WindowTwentyOneEntry.normalizeProgram
    (by decide) pcA1637
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2086 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 1541 92 2086 WindowTwentyOneTableBuild.program
    (by decide) pcA1645
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_init :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2202 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 1633 18 2202 WindowTwentyOneInit.program
    (by decide) pcA1737
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_iteration :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2227 WindowTwentyOneLoop.iterationProgram :=
  WindowTwentyOneSlice.block allWellFormed 1651 438 2227 WindowTwentyOneLoop.iterationProgram
    (by decide) pcA1755
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2690 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 2089 5 2690 WindowTwentyOneReturn.program
    (by decide) pcA2193
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_zeroReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2696 WindowTwentyOneReturn.zeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 2094 7 2696 WindowTwentyOneReturn.zeroProgram
    (by decide) pcA2198
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4752 FermatProgram.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 3609 14 4752 FermatProgram.primeProgram (by decide) pcA3688
    (by rw [locations_map_instruction]; rfl) (by decide)
private def fermat_exponent : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4805 FermatProgram.exponentProgram :=
  WindowTwentyOneSlice.block allWellFormed 3623 9 4805 FermatProgram.exponentProgram (by decide) pcA3702
    (by rw [locations_map_instruction]; rfl) (by decide)
private def fermat_result : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4817 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 3632 16 4817 FermatProgram.returnProgram (by decide) pcA3711
    (by rw [locations_map_instruction]; rfl) (by decide)
def fermatPaths : FermatProgram.Paths submissionArtifact .Osaka where
  prime := fermat_prime
  exponent := fermat_exponent
  result := fermat_result
  legacyJump := by exact isValidJumpDest_index 1525 (by rfl)

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
    have h := isValidJumpDest_index 3609 (by rfl)
    exact h
  zeroJump := by
    have h := isValidJumpDest_index 2094 (by rfl)
    exact h
  loopJump := by
    have h := isValidJumpDest_index 1651 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 430 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
