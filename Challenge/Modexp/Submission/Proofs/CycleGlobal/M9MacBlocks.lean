import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.M9MacPrograms
import Challenge.Modexp.Submission.Proofs.Fast.M9MacRun
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
namespace CycleSubmission.Global.Fast.M9Mac
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.Global.Fast
open Challenge.Modexp.Submission.Proofs.Fast.M9Mac
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
def block0 : Block CycleSubmission.Artifact.artifact .Osaka 8546 (rideTopProgramNP 10 2336) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6407 16 8546 (rideTopProgramNP 10 2336)
    (by change 6407+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block1 : Block CycleSubmission.Artifact.artifact .Osaka 8564 (rideProgram 10 2304) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6423 28 8564 (rideProgram 10 2304)
    (by change 6423+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block2 : Block CycleSubmission.Artifact.artifact .Osaka 8596 (rideProgram 9 2272) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6451 28 8596 (rideProgram 9 2272)
    (by change 6451+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block3 : Block CycleSubmission.Artifact.artifact .Osaka 8628 (rideProgram 8 2240) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6479 28 8628 (rideProgram 8 2240)
    (by change 6479+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block4 : Block CycleSubmission.Artifact.artifact .Osaka 8660 (rideProgram 7 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6507 28 8660 (rideProgram 7 2208)
    (by change 6507+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block5 : Block CycleSubmission.Artifact.artifact .Osaka 8692 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6535 28 8692 (rideProgram 6 2176)
    (by change 6535+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block6 : Block CycleSubmission.Artifact.artifact .Osaka 8724 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6563 28 8724 (rideProgram 5 2144)
    (by change 6563+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block7 : Block CycleSubmission.Artifact.artifact .Osaka 8756 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6591 30 8756 (blockProgram 1280 2112)
    (by change 6591+30 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def exitBlock : Block CycleSubmission.Artifact.artifact .Osaka 8792 exitProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 6621 0 8792 exitProgram
    (by change 6621+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def zero4Block : Block CycleSubmission.Artifact.artifact .Osaka 626 (rideTopProgramNP 6 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 440 16 626 (rideTopProgramNP 6 2208)
    (by change 440+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
set_option maxHeartbeats 4000000 in
def block5c : Block CycleSubmission.Artifact.artifact .Osaka 644 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 456 28 644 (rideProgram 6 2176)
    (by change 456+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
set_option maxHeartbeats 4000000 in
def block6c : Block CycleSubmission.Artifact.artifact .Osaka 676 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 484 28 676 (rideProgram 5 2144)
    (by change 484+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
set_option maxHeartbeats 4000000 in
def block7c : Block CycleSubmission.Artifact.artifact .Osaka 708 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 512 30 708 (blockProgram 1280 2112)
    (by change 512+30 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
end CycleSubmission.Global.Fast.M9Mac
