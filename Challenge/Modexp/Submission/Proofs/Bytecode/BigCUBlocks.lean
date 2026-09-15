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
  entry := WindowTwentyOneSlice.block Artifact.allWellFormed 334 2 484 BigC.Unsigned.entryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  init := WindowTwentyOneSlice.block Artifact.allWellFormed 336 4 488 BigC.Unsigned.initProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  cell := WindowTwentyOneSlice.block Artifact.allWellFormed 340 33 494 BigC.Unsigned.cellProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  guard := WindowTwentyOneSlice.block Artifact.allWellFormed 373 3 529 BigC.Unsigned.guardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  decide := WindowTwentyOneSlice.block Artifact.allWellFormed 376 3 534 BigC.Unsigned.decideProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  retry := WindowTwentyOneSlice.block Artifact.allWellFormed 379 5 539 BigC.Unsigned.retryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  finish := WindowTwentyOneSlice.block Artifact.allWellFormed 384 5 548 BigC.Unsigned.finishProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumpInit := Artifact.isValidJumpDest_index 336 (by rfl)
  jumpLoop := Artifact.isValidJumpDest_index 340 (by rfl)
  jumpDone := Artifact.isValidJumpDest_index 384 (by rfl)

def mulBlocks : BigC.U.MulBlocks Artifact.submissionArtifact where
  mEntry := WindowTwentyOneSlice.block Artifact.allWellFormed 283 7 413 BigC.U.mEntryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mGuard := WindowTwentyOneSlice.block Artifact.allWellFormed 290 8 421 BigC.U.mGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mDouble := WindowTwentyOneSlice.block Artifact.allWellFormed 298 4 432 BigC.U.mDoubleProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m2 := WindowTwentyOneSlice.block Artifact.allWellFormed 302 16 440 BigC.U.m2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mAdd := WindowTwentyOneSlice.block Artifact.allWellFormed 318 4 461 BigC.U.mAddProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m3 := WindowTwentyOneSlice.block Artifact.allWellFormed 322 5 469 BigC.U.m3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m9 := WindowTwentyOneSlice.block Artifact.allWellFormed 327 7 477 BigC.U.m9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j419 := Artifact.isValidJumpDest_index 290 (by rfl)
      j438 := Artifact.isValidJumpDest_index 302 (by rfl)
      j467 := Artifact.isValidJumpDest_index 322 (by rfl)
      j475 := Artifact.isValidJumpDest_index 327 (by rfl)
      j482 := Artifact.isValidJumpDest_index 334 (by rfl) }

def expBlocks : BigC.U.ExpBlocks Artifact.submissionArtifact where
  eGuard := WindowTwentyOneSlice.block Artifact.allWellFormed 220 8 312 BigC.U.eGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eSquare := WindowTwentyOneSlice.block Artifact.allWellFormed 228 6 323 BigC.U.eSquareProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e2 := WindowTwentyOneSlice.block Artifact.allWellFormed 234 23 335 BigC.U.e2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eMul := WindowTwentyOneSlice.block Artifact.allWellFormed 257 7 366 BigC.U.eMulProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e4 := WindowTwentyOneSlice.block Artifact.allWellFormed 264 5 381 BigC.U.e4Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e3 := WindowTwentyOneSlice.block Artifact.allWellFormed 269 5 388 BigC.U.e3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e9 := WindowTwentyOneSlice.block Artifact.allWellFormed 274 9 396 BigC.U.e9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j295 := Artifact.isValidJumpDest_index 208 (by rfl)
      j310 := Artifact.isValidJumpDest_index 220 (by rfl)
      j333 := Artifact.isValidJumpDest_index 234 (by rfl)
      j379 := Artifact.isValidJumpDest_index 264 (by rfl)
      j386 := Artifact.isValidJumpDest_index 269 (by rfl)
      j394 := Artifact.isValidJumpDest_index 274 (by rfl)
      j411 := Artifact.isValidJumpDest_index 283 (by rfl)
      j482 := Artifact.isValidJumpDest_index 334 (by rfl) }

def setupBlocks : BigC.U.SetupBlocks Artifact.submissionArtifact where
  setup := WindowTwentyOneSlice.block Artifact.allWellFormed 165 25 238 BigC.U.setupProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zLoop := WindowTwentyOneSlice.block Artifact.allWellFormed 190 15 273 BigC.U.zLoopProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zExit := WindowTwentyOneSlice.block Artifact.allWellFormed 205 3 292 BigC.U.zExitProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zeroRet := WindowTwentyOneSlice.block Artifact.allWellFormed 208 4 297 BigC.U.zeroRetProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  nz := WindowTwentyOneSlice.block Artifact.allWellFormed 212 8 301 BigC.U.nzProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j236 := Artifact.isValidJumpDest_index 165 (by rfl)
      j271 := Artifact.isValidJumpDest_index 190 (by rfl)
      j295 := Artifact.isValidJumpDest_index 208 (by rfl)
      j299 := Artifact.isValidJumpDest_index 212 (by rfl) }

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.UBlocks
