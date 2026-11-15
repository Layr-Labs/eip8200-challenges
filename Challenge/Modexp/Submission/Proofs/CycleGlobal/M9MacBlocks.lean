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
def block0 : Block CycleSubmission.Artifact.artifact .Osaka 2972 (rideTopProgramNP 10 2336) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2269 16 2972 (rideTopProgramNP 10 2336)
    (by change 2269+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block1 : Block CycleSubmission.Artifact.artifact .Osaka 2990 (rideProgram 10 2304) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2285 28 2990 (rideProgram 10 2304)
    (by change 2285+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block2 : Block CycleSubmission.Artifact.artifact .Osaka 3022 (rideProgram 9 2272) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2313 28 3022 (rideProgram 9 2272)
    (by change 2313+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block3 : Block CycleSubmission.Artifact.artifact .Osaka 3054 (rideProgram 8 2240) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2341 28 3054 (rideProgram 8 2240)
    (by change 2341+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block4 : Block CycleSubmission.Artifact.artifact .Osaka 3086 (rideProgram 7 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2369 28 3086 (rideProgram 7 2208)
    (by change 2369+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block5 : Block CycleSubmission.Artifact.artifact .Osaka 3118 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2397 28 3118 (rideProgram 6 2176)
    (by change 2397+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block6 : Block CycleSubmission.Artifact.artifact .Osaka 3150 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2425 28 3150 (rideProgram 5 2144)
    (by change 2425+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def block7 : Block CycleSubmission.Artifact.artifact .Osaka 3182 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2453 30 3182 (blockProgram 1280 2112)
    (by change 2453+30 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def exitBlock : Block CycleSubmission.Artifact.artifact .Osaka 3218 exitProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2483 0 3218 exitProgram
    (by change 2483+0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def zero4Block : Block CycleSubmission.Artifact.artifact .Osaka 10808 (rideTopProgramNP 6 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8159 16 10808 (rideTopProgramNP 6 2208)
    (by change 8159+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
set_option maxHeartbeats 4000000 in
def block5c : Block CycleSubmission.Artifact.artifact .Osaka 10826 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8175 28 10826 (rideProgram 6 2176)
    (by change 8175+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
set_option maxHeartbeats 4000000 in
def block6c : Block CycleSubmission.Artifact.artifact .Osaka 10858 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8203 28 10858 (rideProgram 5 2144)
    (by change 8203+28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
set_option maxHeartbeats 4000000 in
def block7c : Block CycleSubmission.Artifact.artifact .Osaka 10890 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8231 30 10890 (blockProgram 1280 2112)
    (by change 8231+30 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
end CycleSubmission.Global.Fast.M9Mac
