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
def unpackFinalBlock : Block Artifact.artifact .Osaka 7652 unpackFinalProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 6060 54 7652 unpackFinalProgram
    (by change 6060+54 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6060+54 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 10399 canonicalsubProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8318 5 10399 canonicalsubProgram
    (by change 8318+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8318+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 10409 packFinalProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8324 82 10409 packFinalProgram
    (by change 8324+82 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8324+82 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 10234 canonicalCompare0Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8212 4 10234 canonicalCompare0Program
    (by change 8212+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8212+4 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 10241 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8216 1 10241 jumpiProgram
    (by change 8216+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8216+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 10242 canonicalCompare1Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8217 4 10242 canonicalCompare1Program
    (by change 8217+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8217+4 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 10248 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8221 1 10248 jumpiProgram
    (by change 8221+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8221+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 10249 canonicalCompare2Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8222 5 10249 canonicalCompare2Program
    (by change 8222+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8222+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 10257 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8227 1 10257 jumpiProgram
    (by change 8227+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8227+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 10258 canonicalCompare3Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8228 5 10258 canonicalCompare3Program
    (by change 8228+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8228+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 10266 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8233 1 10266 jumpiProgram
    (by change 8233+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8233+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 10267 canonicalCompare4Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8234 5 10267 canonicalCompare4Program
    (by change 8234+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8234+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 10275 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8239 1 10275 jumpiProgram
    (by change 8239+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8239+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 10276 canonicalCompare5Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8240 5 10276 canonicalCompare5Program
    (by change 8240+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8240+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 10284 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8245 1 10284 jumpiProgram
    (by change 8245+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8245+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 10285 canonicalCompare6Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8246 5 10285 canonicalCompare6Program
    (by change 8246+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8246+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 10293 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8251 1 10293 jumpiProgram
    (by change 8251+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8251+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 10294 canonicalCompare7Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8252 5 10294 canonicalCompare7Program
    (by change 8252+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8252+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 10302 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8257 1 10302 jumpiProgram
    (by change 8257+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8257+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 10303 canonicalCompare8Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8258 5 10303 canonicalCompare8Program
    (by change 8258+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8258+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 10311 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8263 1 10311 jumpiProgram
    (by change 8263+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8263+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 10312 canonicalCompare9Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8264 5 10312 canonicalCompare9Program
    (by change 8264+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8264+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 10320 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8269 1 10320 jumpiProgram
    (by change 8269+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8269+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 10321 canonicalCompare10Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8270 5 10321 canonicalCompare10Program
    (by change 8270+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8270+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 10329 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8275 1 10329 jumpiProgram
    (by change 8275+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8275+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 10330 canonicalCompare11Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8276 5 10330 canonicalCompare11Program
    (by change 8276+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8276+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 10338 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8281 1 10338 jumpiProgram
    (by change 8281+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8281+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 10339 canonicalCompare12Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8282 4 10339 canonicalCompare12Program
    (by change 8282+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8282+4 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 10345 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8286 1 10345 jumpiProgram
    (by change 8286+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8286+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 10346 canonicalCompare13Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8287 4 10346 canonicalCompare13Program
    (by change 8287+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8287+4 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 10352 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8291 1 10352 jumpiProgram
    (by change 8291+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8291+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 10353 canonicalCompare14Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8292 5 10353 canonicalCompare14Program
    (by change 8292+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8292+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 10362 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8297 1 10362 jumpiProgram
    (by change 8297+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8297+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 10363 canonicalCompare15Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8298 5 10363 canonicalCompare15Program
    (by change 8298+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8298+5 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 10372 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8303 1 10372 jumpiProgram
    (by change 8303+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8303+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 10373 canonicalCompare16Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8304 6 10373 canonicalCompare16Program
    (by change 8304+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8304+6 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 10385 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8310 1 10385 jumpiProgram
    (by change 8310+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8310+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 10386 canonicalCompare17Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8311 6 10386 canonicalCompare17Program
    (by change 8311+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8311+6 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17JumpBlock : Block Artifact.artifact .Osaka 10398 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8317 1 10398 jumpiProgram
    (by change 8317+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8317+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 10408 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8323 1 10408 jumpProgram
    (by change 8323+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8323+1 ≤ 8624)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 10399 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8318
    (show Artifact.instructions[8318]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8318 = 10399 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 10409 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8324
    (show Artifact.instructions[8324]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8324 = 10409 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 10556 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8413
    (show Artifact.instructions[8413]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8413 = 10556 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
