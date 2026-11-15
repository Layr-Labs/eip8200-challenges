import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.UnpackFinal
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Canonicalsub
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.PackFinal
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare0
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare1
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare2
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare3
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare4
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare5
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare6
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare7
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare8
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare9
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare10
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare11
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare12
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare13
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare14
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare15
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare16
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.CanonicalCompare17
import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.CRT.CRTControlBase
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 12000000
namespace CycleSubmission.FinalBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open CycleSubmission.Execution HistoricalSearch.CRTControl Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowTwentyOneBinding WindowTwentyOneSlice
def unpackFinalBlock : Block Artifact.artifact .Osaka 5866 unpackFinalProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4269 54 5866 unpackFinalProgram
    (by change 4269+54 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 8542 canonicalsubProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6468 5 8542 canonicalsubProgram
    (by change 6468+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 8552 packFinalProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6474 34 8552 packFinalProgram
    (by change 6474+34 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 8381 canonicalCompare0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6363 4 8381 canonicalCompare0Program
    (by change 6363+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 8387 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6367 1 8387 jumpiProgram
    (by change 6367+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 8388 canonicalCompare1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6368 4 8388 canonicalCompare1Program
    (by change 6368+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 8394 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6372 1 8394 jumpiProgram
    (by change 6372+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 8395 canonicalCompare2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6373 5 8395 canonicalCompare2Program
    (by change 6373+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 8403 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6378 1 8403 jumpiProgram
    (by change 6378+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 8404 canonicalCompare3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6379 5 8404 canonicalCompare3Program
    (by change 6379+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 8412 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6384 1 8412 jumpiProgram
    (by change 6384+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 8413 canonicalCompare4Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6385 5 8413 canonicalCompare4Program
    (by change 6385+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 8421 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6390 1 8421 jumpiProgram
    (by change 6390+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 8422 canonicalCompare5Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6391 5 8422 canonicalCompare5Program
    (by change 6391+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 8430 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6396 1 8430 jumpiProgram
    (by change 6396+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 8431 canonicalCompare6Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6397 5 8431 canonicalCompare6Program
    (by change 6397+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 8439 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6402 1 8439 jumpiProgram
    (by change 6402+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 8440 canonicalCompare7Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6403 5 8440 canonicalCompare7Program
    (by change 6403+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 8448 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6408 1 8448 jumpiProgram
    (by change 6408+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 8449 canonicalCompare8Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6409 5 8449 canonicalCompare8Program
    (by change 6409+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 8457 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6414 1 8457 jumpiProgram
    (by change 6414+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 8458 canonicalCompare9Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6415 5 8458 canonicalCompare9Program
    (by change 6415+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 8466 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6420 1 8466 jumpiProgram
    (by change 6420+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 8467 canonicalCompare10Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6421 5 8467 canonicalCompare10Program
    (by change 6421+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 8475 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6426 1 8475 jumpiProgram
    (by change 6426+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 8476 canonicalCompare11Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6427 5 8476 canonicalCompare11Program
    (by change 6427+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 8484 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6432 1 8484 jumpiProgram
    (by change 6432+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 8485 canonicalCompare12Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6433 4 8485 canonicalCompare12Program
    (by change 6433+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 8491 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6437 1 8491 jumpiProgram
    (by change 6437+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 8492 canonicalCompare13Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6438 4 8492 canonicalCompare13Program
    (by change 6438+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 8498 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6442 1 8498 jumpiProgram
    (by change 6442+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 8499 canonicalCompare14Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6443 5 8499 canonicalCompare14Program
    (by change 6443+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 8508 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6448 1 8508 jumpiProgram
    (by change 6448+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 8509 canonicalCompare15Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6449 5 8509 canonicalCompare15Program
    (by change 6449+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 8518 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6454 1 8518 jumpiProgram
    (by change 6454+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 8519 canonicalCompare16Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6455 6 8519 canonicalCompare16Program
    (by change 6455+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 8531 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6461 1 8531 jumpiProgram
    (by change 6461+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 8532 canonicalCompare17Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6462 6 8532 canonicalCompare17Program
    (by change 6462+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 8551 jumpProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6473 1 8551 jumpProgram
    (by change 6473+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 8542 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 6468
    (show Artifact.instructions[6468]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 6468 = 8542 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 8552 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 6474
    (show Artifact.instructions[6474]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 6474 = 8552 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 10562 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 7993
    (show Artifact.instructions[7993]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 7993 = 10562 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
