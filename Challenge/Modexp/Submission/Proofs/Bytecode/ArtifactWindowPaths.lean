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
each `k`; on a 3,1037-instruction list that is `O(start)` work per instruction, and the two
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
private theorem pcA1612 : Artifact.submissionArtifact.instructionPC 1647 = 2223 := by rfl

private theorem pcA1627 : Artifact.submissionArtifact.instructionPC 1662 = 2243 := by
  rw [show (1662 : Nat) = 1647 + 15 from rfl, instructionPC_add, pcA1612]; rfl

private theorem pcA1629 : Artifact.submissionArtifact.instructionPC 1664 = 2247 := by
  rw [show (1664 : Nat) = 1662 + 2 from rfl, instructionPC_add, pcA1627]; rfl

private theorem pcA1631 : Artifact.submissionArtifact.instructionPC 1665 = 2248 := by
  rw [show (1665 : Nat) = 1664 + 1 from rfl, instructionPC_add, pcA1629]; rfl

private theorem pcA1637 : Artifact.submissionArtifact.instructionPC 1669 = 2254 := by
  rw [show (1669 : Nat) = 1665 + 4 from rfl, instructionPC_add, pcA1631]; rfl

private theorem pcA1645 : Artifact.submissionArtifact.instructionPC 1677 = 2264 := by
  rw [show (1677 : Nat) = 1669 + 8 from rfl, instructionPC_add, pcA1637]; rfl

private theorem pcA1737 : Artifact.submissionArtifact.instructionPC 1769 = 2380 := by
  rw [show (1769 : Nat) = 1677 + 92 from rfl, instructionPC_add, pcA1645]; rfl

private theorem pcA1755 : Artifact.submissionArtifact.instructionPC 1785 = 2401 := by
  rw [show (1785 : Nat) = 1769 + 16 from rfl, instructionPC_add, pcA1737]; rfl

private theorem pcA2193 : Artifact.submissionArtifact.instructionPC 2223 = 2864 := by rfl

private theorem pcA2198 : Artifact.submissionArtifact.instructionPC 2228 = 2870 := by
  rw [show (2228 : Nat) = 2223 + 5 from rfl, instructionPC_add, pcA2193]; rfl

private theorem pcA3688 : Artifact.submissionArtifact.instructionPC 3834 = 4955 := by rfl

private theorem pcA3702 : Artifact.submissionArtifact.instructionPC 3848 = 5008 := by
  rw [show (3848 : Nat) = 3834 + 14 from rfl, instructionPC_add, pcA3688]; rfl

private theorem pcA3711 : Artifact.submissionArtifact.instructionPC 3857 = 5020 := by
  rw [show (3857 : Nat) = 3848 + 9 from rfl, instructionPC_add, pcA3702]; rfl


private def nine_width :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2223 WindowTwentyOneEntry.widthProgram :=
  WindowTwentyOneSlice.block allWellFormed 1647 15 2223 WindowTwentyOneEntry.widthProgram
    (by decide) pcA1612
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_miss :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2243 WindowTwentyOneEntry.missProgram :=
  WindowTwentyOneSlice.block allWellFormed 1662 2 2243 WindowTwentyOneEntry.missProgram
    (by decide) pcA1627
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_base :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2247 WindowTwentyOneEntry.baseProgram :=
  WindowTwentyOneSlice.block allWellFormed 1664 1 2247 WindowTwentyOneEntry.baseProgram
    (by decide) pcA1629
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_modulus :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2248 WindowTwentyOneEntry.modulusProgram :=
  WindowTwentyOneSlice.block allWellFormed 1665 4 2248 WindowTwentyOneEntry.modulusProgram
    (by decide) pcA1631
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_normalize :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2254 WindowTwentyOneEntry.normalizeProgram :=
  WindowTwentyOneSlice.block allWellFormed 1669 8 2254 WindowTwentyOneEntry.normalizeProgram
    (by decide) pcA1637
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_table :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2264 WindowTwentyOneTableBuild.program :=
  WindowTwentyOneSlice.block allWellFormed 1677 92 2264 WindowTwentyOneTableBuild.program
    (by decide) pcA1645
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_init :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2380 WindowTwentyOneInit.program :=
  WindowTwentyOneSlice.block allWellFormed 1769 16 2380 WindowTwentyOneInit.program
    (by decide) pcA1737
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_iteration :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2401 WindowTwentyOneLoop.iterationProgram :=
  WindowTwentyOneSlice.block allWellFormed 1785 438 2401 WindowTwentyOneLoop.iterationProgram
    (by decide) pcA1755
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_finish :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2864 WindowTwentyOneReturn.program :=
  WindowTwentyOneSlice.block allWellFormed 2223 5 2864 WindowTwentyOneReturn.program
    (by decide) pcA2193
    (by rw [locations_map_instruction]; rfl) (by decide)

private def nine_zeroReturn :
    WindowTwentyOneBinding.Block submissionArtifact .Osaka 2870 WindowTwentyOneReturn.zeroProgram :=
  WindowTwentyOneSlice.block allWellFormed 2228 7 2870 WindowTwentyOneReturn.zeroProgram
    (by decide) pcA2198
    (by rw [locations_map_instruction]; rfl) (by decide)

private def fermat_prime : WindowTwentyOneBinding.Block submissionArtifact .Osaka 4955 FermatProgram.primeProgram :=
  WindowTwentyOneSlice.block allWellFormed 3834 14 4955 FermatProgram.primeProgram (by decide) pcA3688
    (by rw [locations_map_instruction]; rfl) (by decide)
private def fermat_exponent : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5008 FermatProgram.exponentProgram :=
  WindowTwentyOneSlice.block allWellFormed 3848 9 5008 FermatProgram.exponentProgram (by decide) pcA3702
    (by rw [locations_map_instruction]; rfl) (by decide)
private def fermat_result : WindowTwentyOneBinding.Block submissionArtifact .Osaka 5020 FermatProgram.returnProgram :=
  WindowTwentyOneSlice.block allWellFormed 3857 16 5020 FermatProgram.returnProgram (by decide) pcA3711
    (by rw [locations_map_instruction]; rfl) (by decide)
def fermatPaths : FermatProgram.Paths submissionArtifact .Osaka where
  prime := fermat_prime
  exponent := fermat_exponent
  result := fermat_result
  legacyJump := by exact isValidJumpDest_index 1664 (by rfl)

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
    have h := isValidJumpDest_index 3834 (by rfl)
    exact h
  zeroJump := by
    have h := isValidJumpDest_index 2228 (by rfl)
    exact h
  loopJump := by
    have h := isValidJumpDest_index 1785 (by rfl)
    exact h
  missJump := by
    have h := isValidJumpDest_index 435 (by rfl)
    exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
