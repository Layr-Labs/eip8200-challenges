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
def unpackFinalBlock : Block Artifact.artifact .Osaka 5843 unpackFinalProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 4277 54 5843 unpackFinalProgram
    (by change 4277+54 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 8519 canonicalsubProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6476 5 8519 canonicalsubProgram
    (by change 6476+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 8529 packFinalProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6482 34 8529 packFinalProgram
    (by change 6482+34 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 8358 canonicalCompare0Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6371 4 8358 canonicalCompare0Program
    (by change 6371+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 8364 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6375 1 8364 jumpiProgram
    (by change 6375+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 8365 canonicalCompare1Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6376 4 8365 canonicalCompare1Program
    (by change 6376+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 8371 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6380 1 8371 jumpiProgram
    (by change 6380+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 8372 canonicalCompare2Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6381 5 8372 canonicalCompare2Program
    (by change 6381+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 8380 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6386 1 8380 jumpiProgram
    (by change 6386+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 8381 canonicalCompare3Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6387 5 8381 canonicalCompare3Program
    (by change 6387+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 8389 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6392 1 8389 jumpiProgram
    (by change 6392+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 8390 canonicalCompare4Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6393 5 8390 canonicalCompare4Program
    (by change 6393+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 8398 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6398 1 8398 jumpiProgram
    (by change 6398+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 8399 canonicalCompare5Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6399 5 8399 canonicalCompare5Program
    (by change 6399+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 8407 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6404 1 8407 jumpiProgram
    (by change 6404+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 8408 canonicalCompare6Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6405 5 8408 canonicalCompare6Program
    (by change 6405+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 8416 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6410 1 8416 jumpiProgram
    (by change 6410+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 8417 canonicalCompare7Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6411 5 8417 canonicalCompare7Program
    (by change 6411+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 8425 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6416 1 8425 jumpiProgram
    (by change 6416+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 8426 canonicalCompare8Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6417 5 8426 canonicalCompare8Program
    (by change 6417+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 8434 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6422 1 8434 jumpiProgram
    (by change 6422+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 8435 canonicalCompare9Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6423 5 8435 canonicalCompare9Program
    (by change 6423+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 8443 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6428 1 8443 jumpiProgram
    (by change 6428+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 8444 canonicalCompare10Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6429 5 8444 canonicalCompare10Program
    (by change 6429+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 8452 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6434 1 8452 jumpiProgram
    (by change 6434+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 8453 canonicalCompare11Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6435 5 8453 canonicalCompare11Program
    (by change 6435+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 8461 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6440 1 8461 jumpiProgram
    (by change 6440+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 8462 canonicalCompare12Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6441 4 8462 canonicalCompare12Program
    (by change 6441+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 8468 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6445 1 8468 jumpiProgram
    (by change 6445+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 8469 canonicalCompare13Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6446 4 8469 canonicalCompare13Program
    (by change 6446+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 8475 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6450 1 8475 jumpiProgram
    (by change 6450+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 8476 canonicalCompare14Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6451 5 8476 canonicalCompare14Program
    (by change 6451+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 8485 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6456 1 8485 jumpiProgram
    (by change 6456+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 8486 canonicalCompare15Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6457 5 8486 canonicalCompare15Program
    (by change 6457+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 8495 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6462 1 8495 jumpiProgram
    (by change 6462+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 8496 canonicalCompare16Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6463 6 8496 canonicalCompare16Program
    (by change 6463+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 8508 jumpiProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6469 1 8508 jumpiProgram
    (by change 6469+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 8509 canonicalCompare17Program :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6470 6 8509 canonicalCompare17Program
    (by change 6470+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 8528 jumpProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6481 1 8528 jumpProgram
    (by change 6481+1 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 8519 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 6476
    (show Artifact.instructions[6476]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 6476 = 8519 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 8529 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 6482
    (show Artifact.instructions[6482]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 6482 = 8529 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 10562 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 7997
    (show Artifact.instructions[7997]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 7997 = 10562 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
