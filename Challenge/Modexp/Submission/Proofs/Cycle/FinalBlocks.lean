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
  WindowTwentyOneSlice.block Artifact.wellFormed 5990 54 7652 unpackFinalProgram
    (by change 5990+54 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 5990+54 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalsubBlock : Block Artifact.artifact .Osaka 10399 canonicalsubProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8223 5 10399 canonicalsubProgram
    (by change 8223+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8223+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def packFinalBlock : Block Artifact.artifact .Osaka 10409 packFinalProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8229 82 10409 packFinalProgram
    (by change 8229+82 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8229+82 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0Block : Block Artifact.artifact .Osaka 10234 canonicalCompare0Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8117 4 10234 canonicalCompare0Program
    (by change 8117+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8117+4 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare0JumpBlock : Block Artifact.artifact .Osaka 10241 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8121 1 10241 jumpiProgram
    (by change 8121+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8121+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1Block : Block Artifact.artifact .Osaka 10242 canonicalCompare1Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8122 4 10242 canonicalCompare1Program
    (by change 8122+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8122+4 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare1JumpBlock : Block Artifact.artifact .Osaka 10248 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8126 1 10248 jumpiProgram
    (by change 8126+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8126+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2Block : Block Artifact.artifact .Osaka 10249 canonicalCompare2Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8127 5 10249 canonicalCompare2Program
    (by change 8127+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8127+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare2JumpBlock : Block Artifact.artifact .Osaka 10257 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8132 1 10257 jumpiProgram
    (by change 8132+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8132+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3Block : Block Artifact.artifact .Osaka 10258 canonicalCompare3Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8133 5 10258 canonicalCompare3Program
    (by change 8133+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8133+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare3JumpBlock : Block Artifact.artifact .Osaka 10266 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8138 1 10266 jumpiProgram
    (by change 8138+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8138+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4Block : Block Artifact.artifact .Osaka 10267 canonicalCompare4Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8139 5 10267 canonicalCompare4Program
    (by change 8139+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8139+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare4JumpBlock : Block Artifact.artifact .Osaka 10275 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8144 1 10275 jumpiProgram
    (by change 8144+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8144+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5Block : Block Artifact.artifact .Osaka 10276 canonicalCompare5Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8145 5 10276 canonicalCompare5Program
    (by change 8145+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8145+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare5JumpBlock : Block Artifact.artifact .Osaka 10284 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8150 1 10284 jumpiProgram
    (by change 8150+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8150+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6Block : Block Artifact.artifact .Osaka 10285 canonicalCompare6Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8151 5 10285 canonicalCompare6Program
    (by change 8151+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8151+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare6JumpBlock : Block Artifact.artifact .Osaka 10293 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8156 1 10293 jumpiProgram
    (by change 8156+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8156+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7Block : Block Artifact.artifact .Osaka 10294 canonicalCompare7Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8157 5 10294 canonicalCompare7Program
    (by change 8157+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8157+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare7JumpBlock : Block Artifact.artifact .Osaka 10302 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8162 1 10302 jumpiProgram
    (by change 8162+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8162+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8Block : Block Artifact.artifact .Osaka 10303 canonicalCompare8Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8163 5 10303 canonicalCompare8Program
    (by change 8163+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8163+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare8JumpBlock : Block Artifact.artifact .Osaka 10311 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8168 1 10311 jumpiProgram
    (by change 8168+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8168+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9Block : Block Artifact.artifact .Osaka 10312 canonicalCompare9Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8169 5 10312 canonicalCompare9Program
    (by change 8169+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8169+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare9JumpBlock : Block Artifact.artifact .Osaka 10320 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8174 1 10320 jumpiProgram
    (by change 8174+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8174+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10Block : Block Artifact.artifact .Osaka 10321 canonicalCompare10Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8175 5 10321 canonicalCompare10Program
    (by change 8175+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8175+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare10JumpBlock : Block Artifact.artifact .Osaka 10329 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8180 1 10329 jumpiProgram
    (by change 8180+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8180+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11Block : Block Artifact.artifact .Osaka 10330 canonicalCompare11Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8181 5 10330 canonicalCompare11Program
    (by change 8181+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8181+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare11JumpBlock : Block Artifact.artifact .Osaka 10338 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8186 1 10338 jumpiProgram
    (by change 8186+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8186+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12Block : Block Artifact.artifact .Osaka 10339 canonicalCompare12Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8187 4 10339 canonicalCompare12Program
    (by change 8187+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8187+4 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare12JumpBlock : Block Artifact.artifact .Osaka 10345 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8191 1 10345 jumpiProgram
    (by change 8191+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8191+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13Block : Block Artifact.artifact .Osaka 10346 canonicalCompare13Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8192 4 10346 canonicalCompare13Program
    (by change 8192+4 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8192+4 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare13JumpBlock : Block Artifact.artifact .Osaka 10352 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8196 1 10352 jumpiProgram
    (by change 8196+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8196+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14Block : Block Artifact.artifact .Osaka 10353 canonicalCompare14Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8197 5 10353 canonicalCompare14Program
    (by change 8197+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8197+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare14JumpBlock : Block Artifact.artifact .Osaka 10362 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8202 1 10362 jumpiProgram
    (by change 8202+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8202+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15Block : Block Artifact.artifact .Osaka 10363 canonicalCompare15Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8203 5 10363 canonicalCompare15Program
    (by change 8203+5 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8203+5 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare15JumpBlock : Block Artifact.artifact .Osaka 10372 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8208 1 10372 jumpiProgram
    (by change 8208+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8208+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16Block : Block Artifact.artifact .Osaka 10373 canonicalCompare16Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8209 6 10373 canonicalCompare16Program
    (by change 8209+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8209+6 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare16JumpBlock : Block Artifact.artifact .Osaka 10385 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8215 1 10385 jumpiProgram
    (by change 8215+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8215+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17Block : Block Artifact.artifact .Osaka 10386 canonicalCompare17Program :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8216 6 10386 canonicalCompare17Program
    (by change 8216+6 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8216+6 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalCompare17JumpBlock : Block Artifact.artifact .Osaka 10398 jumpiProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8222 1 10398 jumpiProgram
    (by change 8222+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8222+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
def canonicalJumpBlock : Block Artifact.artifact .Osaka 10408 jumpProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 8228 1 10408 jumpProgram
    (by change 8228+1 ≤ Artifact.instructions.length
        exact Nat.le_trans (by decide : 8228+1 ≤ 8670)
          (Nat.le_of_eq Artifact.instructionCount.symm))
    (by rw [PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
theorem validJump10857 : Decode.isValidJumpDest Artifact.bytecode 10399 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8223
    (show Artifact.instructions[8223]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8223 = 10399 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump10867 : Decode.isValidJumpDest Artifact.bytecode 10409 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8229
    (show Artifact.instructions[8229]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8229 = 10409 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
theorem validJump11014 : Decode.isValidJumpDest Artifact.bytecode 10556 = true := by
  have h := ProgramArtifact.isValidJumpDest_index Artifact.artifact 8318
    (show Artifact.instructions[8318]? = some (.op .JUMPDEST) by rfl)
  have hp : Artifact.artifact.instructionPC 8318 = 10556 := by
    rw [PCFast.instructionPC_eq_byteLength]; rfl
  rw [hp] at h
  exact h
end CycleSubmission.FinalBlocks
