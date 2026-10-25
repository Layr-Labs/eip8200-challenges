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
  WindowTwentyOneSlice.block Artifact.wellFormed 6060 55 7652 unpackFinalProgram
    (by change 6060+55 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 6060+55 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 10399 canonicalsubProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8320 5 10399 canonicalsubProgram
    (by change 8320+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8320+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 10409 packFinalProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8326 87 10409 packFinalProgram
    (by change 8326+87 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8326+87 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 10234 canonicalCompare0Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8213 5 10234 canonicalCompare0Program
    (by change 8213+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8213+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 10241 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8218 1 10241 jumpiProgram
    (by change 8218+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8218+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 10242 canonicalCompare1Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8219 4 10242 canonicalCompare1Program
    (by change 8219+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8219+4 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 10248 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8223 1 10248 jumpiProgram
    (by change 8223+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8223+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 10249 canonicalCompare2Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8224 5 10249 canonicalCompare2Program
    (by change 8224+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8224+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 10257 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8229 1 10257 jumpiProgram
    (by change 8229+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8229+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 10258 canonicalCompare3Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8230 5 10258 canonicalCompare3Program
    (by change 8230+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8230+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 10266 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8235 1 10266 jumpiProgram
    (by change 8235+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8235+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 10267 canonicalCompare4Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8236 5 10267 canonicalCompare4Program
    (by change 8236+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8236+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 10275 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8241 1 10275 jumpiProgram
    (by change 8241+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8241+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 10276 canonicalCompare5Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8242 5 10276 canonicalCompare5Program
    (by change 8242+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8242+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 10284 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8247 1 10284 jumpiProgram
    (by change 8247+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8247+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 10285 canonicalCompare6Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8248 5 10285 canonicalCompare6Program
    (by change 8248+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8248+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 10293 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8253 1 10293 jumpiProgram
    (by change 8253+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8253+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 10294 canonicalCompare7Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8254 5 10294 canonicalCompare7Program
    (by change 8254+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8254+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 10302 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8259 1 10302 jumpiProgram
    (by change 8259+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8259+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 10303 canonicalCompare8Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8260 5 10303 canonicalCompare8Program
    (by change 8260+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8260+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 10311 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8265 1 10311 jumpiProgram
    (by change 8265+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8265+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 10312 canonicalCompare9Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8266 5 10312 canonicalCompare9Program
    (by change 8266+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8266+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 10320 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8271 1 10320 jumpiProgram
    (by change 8271+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8271+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 10321 canonicalCompare10Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8272 5 10321 canonicalCompare10Program
    (by change 8272+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8272+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 10329 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8277 1 10329 jumpiProgram
    (by change 8277+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8277+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 10330 canonicalCompare11Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8278 5 10330 canonicalCompare11Program
    (by change 8278+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8278+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 10338 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8283 1 10338 jumpiProgram
    (by change 8283+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8283+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 10339 canonicalCompare12Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8284 4 10339 canonicalCompare12Program
    (by change 8284+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8284+4 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 10345 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8288 1 10345 jumpiProgram
    (by change 8288+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8288+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 10346 canonicalCompare13Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8289 4 10346 canonicalCompare13Program
    (by change 8289+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8289+4 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 10352 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8293 1 10352 jumpiProgram
    (by change 8293+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8293+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 10353 canonicalCompare14Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8294 5 10353 canonicalCompare14Program
    (by change 8294+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8294+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 10362 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8299 1 10362 jumpiProgram
    (by change 8299+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8299+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 10363 canonicalCompare15Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8300 5 10363 canonicalCompare15Program
    (by change 8300+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8300+5 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 10372 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8305 1 10372 jumpiProgram
    (by change 8305+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8305+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 10373 canonicalCompare16Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8306 6 10373 canonicalCompare16Program
    (by change 8306+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8306+6 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 10385 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8312 1 10385 jumpiProgram
    (by change 8312+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8312+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 10386 canonicalCompare17Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8313 6 10386 canonicalCompare17Program
    (by change 8313+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8313+6 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17JumpBlock : Block Artifact.artifact .Osaka 10398 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8319 1 10398 jumpiProgram
    (by change 8319+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8319+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 10408 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8325 1 10408 jumpProgram
    (by change 8325+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8325+1 ≤ 8543)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 10399 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8320
    (show Artifact.instructions[8320]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8320 = 10399 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 10409 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8326
    (show Artifact.instructions[8326]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8326 = 10409 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 10556 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8421
    (show Artifact.instructions[8421]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8421 = 10556 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
