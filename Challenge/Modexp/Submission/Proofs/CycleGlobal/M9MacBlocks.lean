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

 







def block0 : Block CycleSubmission.Artifact.artifact .Osaka 2780 (rideTopProgramNP 10 2336) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2123 16 2780 (rideTopProgramNP 10 2336)
    (by change 2123 + 16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

 

def block1 : Block CycleSubmission.Artifact.artifact .Osaka 2798 (rideProgram 10 2304) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2139 28 2798 (rideProgram 10 2304)
    (by change 2139 + 28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

 

def block2 : Block CycleSubmission.Artifact.artifact .Osaka 2830 (rideProgram 9 2272) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2167 28 2830 (rideProgram 9 2272)
    (by change 2167 + 28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

 

def block3 : Block CycleSubmission.Artifact.artifact .Osaka 2862 (rideProgram 8 2240) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2195 28 2862 (rideProgram 8 2240)
    (by change 2195 + 28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

 

def block4 : Block CycleSubmission.Artifact.artifact .Osaka 2894 (rideProgram 7 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2223 28 2894 (rideProgram 7 2208)
    (by change 2223 + 28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

 

def block5 : Block CycleSubmission.Artifact.artifact .Osaka 2926 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2251 28 2926 (rideProgram 6 2176)
    (by change 2251 + 28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

 

def block6 : Block CycleSubmission.Artifact.artifact .Osaka 2958 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2279 28 2958 (rideProgram 5 2144)
    (by change 2279 + 28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

 

def block7 : Block CycleSubmission.Artifact.artifact .Osaka 2990 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2307 30 2990 (blockProgram 1280 2112)
    (by change 2307 + 30 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

 
def exitBlock : Block CycleSubmission.Artifact.artifact .Osaka 3026 exitProgram :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2337 0 3026 exitProgram
    (by change 2337 + 0 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

 
def zero4Block : Block CycleSubmission.Artifact.artifact .Osaka 10795 (rideTopProgramNP 6 2208) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8299 16 10795 (rideTopProgramNP 6 2208)
    (by change 8299 + 16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

set_option maxHeartbeats 4000000 in
 
def block5c : Block CycleSubmission.Artifact.artifact .Osaka 10813 (rideProgram 6 2176) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8315 28 10813 (rideProgram 6 2176)
    (by change 8315 + 28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

set_option maxHeartbeats 4000000 in
def block6c : Block CycleSubmission.Artifact.artifact .Osaka 10845 (rideProgram 5 2144) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8343 28 10845 (rideProgram 5 2144)
    (by change 8343 + 28 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

set_option maxHeartbeats 4000000 in
def block7c : Block CycleSubmission.Artifact.artifact .Osaka 10877 (blockProgram 1280 2112) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 8371 30 10877 (blockProgram 1280 2112)
    (by change 8371 + 30 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)

end CycleSubmission.Global.Fast.M9Mac

