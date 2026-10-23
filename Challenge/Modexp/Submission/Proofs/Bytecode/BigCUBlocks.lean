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
  entry := WindowTwentyOneSlice.block Artifact.allWellFormed 315 2 464 BigC.Unsigned.entryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  init := WindowTwentyOneSlice.block Artifact.allWellFormed 317 4 468 BigC.Unsigned.initProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  cell := WindowTwentyOneSlice.block Artifact.allWellFormed 321 32 474 BigC.Unsigned.cellProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  guard := WindowTwentyOneSlice.block Artifact.allWellFormed 353 3 509 BigC.Unsigned.guardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  decide := WindowTwentyOneSlice.block Artifact.allWellFormed 356 3 514 BigC.Unsigned.decideProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  retry := WindowTwentyOneSlice.block Artifact.allWellFormed 359 5 519 BigC.Unsigned.retryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  finish := WindowTwentyOneSlice.block Artifact.allWellFormed 364 5 528 BigC.Unsigned.finishProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumpInit := Artifact.isValidJumpDest_index 317 (by rfl)
  jumpLoop := Artifact.isValidJumpDest_index 321 (by rfl)
  jumpDone := Artifact.isValidJumpDest_index 364 (by rfl)

def mulBlocks : BigC.U.MulBlocks Artifact.submissionArtifact where
  mEntry := WindowTwentyOneSlice.block Artifact.allWellFormed 264 7 393 BigC.U.mEntryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mGuard := WindowTwentyOneSlice.block Artifact.allWellFormed 271 8 401 BigC.U.mGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mDouble := WindowTwentyOneSlice.block Artifact.allWellFormed 279 4 412 BigC.U.mDoubleProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m2 := WindowTwentyOneSlice.block Artifact.allWellFormed 283 16 420 BigC.U.m2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mAdd := WindowTwentyOneSlice.block Artifact.allWellFormed 299 4 441 BigC.U.mAddProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m3 := WindowTwentyOneSlice.block Artifact.allWellFormed 303 5 449 BigC.U.m3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m9 := WindowTwentyOneSlice.block Artifact.allWellFormed 308 7 457 BigC.U.m9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j419 := Artifact.isValidJumpDest_index 271 (by rfl)
      j438 := Artifact.isValidJumpDest_index 283 (by rfl)
      j467 := Artifact.isValidJumpDest_index 303 (by rfl)
      j475 := Artifact.isValidJumpDest_index 308 (by rfl)
      j482 := Artifact.isValidJumpDest_index 315 (by rfl) }

def expBlocks : BigC.U.ExpBlocks Artifact.submissionArtifact where
  eGuard := WindowTwentyOneSlice.block Artifact.allWellFormed 201 8 292 BigC.U.eGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eSquare := WindowTwentyOneSlice.block Artifact.allWellFormed 209 6 303 BigC.U.eSquareProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e2 := WindowTwentyOneSlice.block Artifact.allWellFormed 215 23 315 BigC.U.e2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eMul := WindowTwentyOneSlice.block Artifact.allWellFormed 238 7 346 BigC.U.eMulProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e4 := WindowTwentyOneSlice.block Artifact.allWellFormed 245 5 361 BigC.U.e4Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e3 := WindowTwentyOneSlice.block Artifact.allWellFormed 250 5 368 BigC.U.e3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e9 := WindowTwentyOneSlice.block Artifact.allWellFormed 255 9 376 BigC.U.e9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j295 := Artifact.isValidJumpDest_index 189 (by rfl)
      j310 := Artifact.isValidJumpDest_index 201 (by rfl)
      j333 := Artifact.isValidJumpDest_index 215 (by rfl)
      j379 := Artifact.isValidJumpDest_index 245 (by rfl)
      j386 := Artifact.isValidJumpDest_index 250 (by rfl)
      j394 := Artifact.isValidJumpDest_index 255 (by rfl)
      j411 := Artifact.isValidJumpDest_index 264 (by rfl)
      j482 := Artifact.isValidJumpDest_index 315 (by rfl) }

def setupBlocks : BigC.U.SetupBlocks Artifact.submissionArtifact where
  setup := WindowTwentyOneSlice.block Artifact.allWellFormed 146 25 219 BigC.U.setupProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zLoop := WindowTwentyOneSlice.block Artifact.allWellFormed 171 15 254 BigC.U.zLoopProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zExit := WindowTwentyOneSlice.block Artifact.allWellFormed 186 3 272 BigC.U.zExitProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zeroRet := WindowTwentyOneSlice.block Artifact.allWellFormed 189 4 277 BigC.U.zeroRetProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  nz := WindowTwentyOneSlice.block Artifact.allWellFormed 193 8 281 BigC.U.nzProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j236 := Artifact.isValidJumpDest_index 146 (by rfl)
      j271 := Artifact.isValidJumpDest_index 171 (by rfl)
      j295 := Artifact.isValidJumpDest_index 189 (by rfl)
      j299 := Artifact.isValidJumpDest_index 193 (by rfl) }

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.UBlocks
