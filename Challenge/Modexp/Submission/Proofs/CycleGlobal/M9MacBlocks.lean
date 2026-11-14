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
def block0 : Block CycleSubmission.Artifact.artifact .Osaka 2941 (rideTopProgramNP 10 2336) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2270 16 2941 (rideTopProgramNP 10 2336)
    (by change 2270+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block1 : Block CycleSubmission.Artifact.artifact .Osaka 2959 (rideProgram 10 2304) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2286 28 2959 (rideProgram 10 2304)
    (by change 2286+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block2 : Block CycleSubmission.Artifact.artifact .Osaka 2991 (rideProgram 9 2272) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2314 28 2991 (rideProgram 9 2272)
    (by change 2314+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block3 : Block CycleSubmission.Artifact.artifact .Osaka 3023 (rideProgram 8 2240) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2342 28 3023 (rideProgram 8 2240)
    (by change 2342+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block4 : Block CycleSubmission.Artifact.artifact .Osaka 3055 (rideProgram 7 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2370 28 3055 (rideProgram 7 2208)
    (by change 2370+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block5 : Block CycleSubmission.Artifact.artifact .Osaka 3087 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2398 28 3087 (rideProgram 6 2176)
    (by change 2398+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block6 : Block CycleSubmission.Artifact.artifact .Osaka 3119 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2426 28 3119 (rideProgram 5 2144)
    (by change 2426+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block7 : Block CycleSubmission.Artifact.artifact .Osaka 3151 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2454 30 3151 (blockProgram 1280 2112)
    (by change 2454+30 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def exitBlock : Block CycleSubmission.Artifact.artifact .Osaka 3187 exitProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2484 0 3187 exitProgram
    (by change 2484+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def zero4Block : Block CycleSubmission.Artifact.artifact .Osaka 10805 (rideTopProgramNP 6 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8164 16 10805 (rideTopProgramNP 6 2208)
    (by change 8164+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
set_option maxHeartbeats 4000000 in
def block5c : Block CycleSubmission.Artifact.artifact .Osaka 10823 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8180 28 10823 (rideProgram 6 2176)
    (by change 8180+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
set_option maxHeartbeats 4000000 in
def block6c : Block CycleSubmission.Artifact.artifact .Osaka 10855 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8208 28 10855 (rideProgram 5 2144)
    (by change 8208+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
set_option maxHeartbeats 4000000 in
def block7c : Block CycleSubmission.Artifact.artifact .Osaka 10887 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8236 30 10887 (blockProgram 1280 2112)
    (by change 8236+30 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
end CycleSubmission.Global.Fast.M9Mac
