import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUnsignedGas
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUMul
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUExpRun
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUSetupRun

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-! Location certificates binding the generic big-modulus ADDM / MULM proofs to the submitted artifact. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigC.UBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

def unsignedBlocks : BigC.Unsigned.Blocks Artifact.submissionArtifact where
  entry := WindowTwentyOneSlice.block Artifact.allWellFormed 332 2 482 BigC.Unsigned.entryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  init := WindowTwentyOneSlice.block Artifact.allWellFormed 334 4 486 BigC.Unsigned.initProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  cell := WindowTwentyOneSlice.block Artifact.allWellFormed 338 33 492 BigC.Unsigned.cellProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  guard := WindowTwentyOneSlice.block Artifact.allWellFormed 371 3 527 BigC.Unsigned.guardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  decide := WindowTwentyOneSlice.block Artifact.allWellFormed 374 3 532 BigC.Unsigned.decideProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  retry := WindowTwentyOneSlice.block Artifact.allWellFormed 377 5 537 BigC.Unsigned.retryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  finish := WindowTwentyOneSlice.block Artifact.allWellFormed 382 5 546 BigC.Unsigned.finishProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumpInit := Artifact.isValidJumpDest_index 334 (by rfl)
  jumpLoop := Artifact.isValidJumpDest_index 338 (by rfl)
  jumpDone := Artifact.isValidJumpDest_index 382 (by rfl)

def mulBlocks : BigC.U.MulBlocks Artifact.submissionArtifact where
  mEntry := WindowTwentyOneSlice.block Artifact.allWellFormed 281 7 411 BigC.U.mEntryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mGuard := WindowTwentyOneSlice.block Artifact.allWellFormed 288 8 419 BigC.U.mGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mDouble := WindowTwentyOneSlice.block Artifact.allWellFormed 296 4 430 BigC.U.mDoubleProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m2 := WindowTwentyOneSlice.block Artifact.allWellFormed 300 16 438 BigC.U.m2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mAdd := WindowTwentyOneSlice.block Artifact.allWellFormed 316 4 459 BigC.U.mAddProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m3 := WindowTwentyOneSlice.block Artifact.allWellFormed 320 5 467 BigC.U.m3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m9 := WindowTwentyOneSlice.block Artifact.allWellFormed 325 7 475 BigC.U.m9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j419 := Artifact.isValidJumpDest_index 288 (by rfl)
      j438 := Artifact.isValidJumpDest_index 300 (by rfl)
      j467 := Artifact.isValidJumpDest_index 320 (by rfl)
      j475 := Artifact.isValidJumpDest_index 325 (by rfl)
      j482 := Artifact.isValidJumpDest_index 332 (by rfl) }

def expBlocks : BigC.U.ExpBlocks Artifact.submissionArtifact where
  eGuard := WindowTwentyOneSlice.block Artifact.allWellFormed 218 8 310 BigC.U.eGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eSquare := WindowTwentyOneSlice.block Artifact.allWellFormed 226 6 321 BigC.U.eSquareProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e2 := WindowTwentyOneSlice.block Artifact.allWellFormed 232 23 333 BigC.U.e2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eMul := WindowTwentyOneSlice.block Artifact.allWellFormed 255 7 364 BigC.U.eMulProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e4 := WindowTwentyOneSlice.block Artifact.allWellFormed 262 5 379 BigC.U.e4Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e3 := WindowTwentyOneSlice.block Artifact.allWellFormed 267 5 386 BigC.U.e3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e9 := WindowTwentyOneSlice.block Artifact.allWellFormed 272 9 394 BigC.U.e9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j295 := Artifact.isValidJumpDest_index 206 (by rfl)
      j310 := Artifact.isValidJumpDest_index 218 (by rfl)
      j333 := Artifact.isValidJumpDest_index 232 (by rfl)
      j379 := Artifact.isValidJumpDest_index 262 (by rfl)
      j386 := Artifact.isValidJumpDest_index 267 (by rfl)
      j394 := Artifact.isValidJumpDest_index 272 (by rfl)
      j411 := Artifact.isValidJumpDest_index 281 (by rfl)
      j482 := Artifact.isValidJumpDest_index 332 (by rfl) }

def setupBlocks : BigC.U.SetupBlocks Artifact.submissionArtifact where
  setup := WindowTwentyOneSlice.block Artifact.allWellFormed 163 25 236 BigC.U.setupProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zLoop := WindowTwentyOneSlice.block Artifact.allWellFormed 188 15 271 BigC.U.zLoopProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zExit := WindowTwentyOneSlice.block Artifact.allWellFormed 203 3 290 BigC.U.zExitProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zeroRet := WindowTwentyOneSlice.block Artifact.allWellFormed 206 4 295 BigC.U.zeroRetProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  nz := WindowTwentyOneSlice.block Artifact.allWellFormed 210 8 299 BigC.U.nzProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j236 := Artifact.isValidJumpDest_index 163 (by rfl)
      j271 := Artifact.isValidJumpDest_index 188 (by rfl)
      j295 := Artifact.isValidJumpDest_index 206 (by rfl)
      j299 := Artifact.isValidJumpDest_index 210 (by rfl) }

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.UBlocks
