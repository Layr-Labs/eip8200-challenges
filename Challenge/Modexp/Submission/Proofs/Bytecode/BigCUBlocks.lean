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
  entry := WindowTwentyOneSlice.block Artifact.allWellFormed 317 2 464 BigC.Unsigned.entryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  init := WindowTwentyOneSlice.block Artifact.allWellFormed 319 4 468 BigC.Unsigned.initProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  cell := WindowTwentyOneSlice.block Artifact.allWellFormed 323 33 474 BigC.Unsigned.cellProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  guard := WindowTwentyOneSlice.block Artifact.allWellFormed 356 3 509 BigC.Unsigned.guardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  decide := WindowTwentyOneSlice.block Artifact.allWellFormed 359 3 514 BigC.Unsigned.decideProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  retry := WindowTwentyOneSlice.block Artifact.allWellFormed 362 5 519 BigC.Unsigned.retryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  finish := WindowTwentyOneSlice.block Artifact.allWellFormed 367 5 528 BigC.Unsigned.finishProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumpInit := Artifact.isValidJumpDest_index 319 (by rfl)
  jumpLoop := Artifact.isValidJumpDest_index 323 (by rfl)
  jumpDone := Artifact.isValidJumpDest_index 367 (by rfl)

def mulBlocks : BigC.U.MulBlocks Artifact.submissionArtifact where
  mEntry := WindowTwentyOneSlice.block Artifact.allWellFormed 266 7 393 BigC.U.mEntryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mGuard := WindowTwentyOneSlice.block Artifact.allWellFormed 273 8 401 BigC.U.mGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mDouble := WindowTwentyOneSlice.block Artifact.allWellFormed 281 4 412 BigC.U.mDoubleProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m2 := WindowTwentyOneSlice.block Artifact.allWellFormed 285 16 420 BigC.U.m2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mAdd := WindowTwentyOneSlice.block Artifact.allWellFormed 301 4 441 BigC.U.mAddProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m3 := WindowTwentyOneSlice.block Artifact.allWellFormed 305 5 449 BigC.U.m3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m9 := WindowTwentyOneSlice.block Artifact.allWellFormed 310 7 457 BigC.U.m9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j419 := Artifact.isValidJumpDest_index 273 (by rfl)
      j438 := Artifact.isValidJumpDest_index 285 (by rfl)
      j467 := Artifact.isValidJumpDest_index 305 (by rfl)
      j475 := Artifact.isValidJumpDest_index 310 (by rfl)
      j482 := Artifact.isValidJumpDest_index 317 (by rfl) }

def expBlocks : BigC.U.ExpBlocks Artifact.submissionArtifact where
  eGuard := WindowTwentyOneSlice.block Artifact.allWellFormed 203 8 292 BigC.U.eGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eSquare := WindowTwentyOneSlice.block Artifact.allWellFormed 211 6 303 BigC.U.eSquareProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e2 := WindowTwentyOneSlice.block Artifact.allWellFormed 217 23 315 BigC.U.e2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eMul := WindowTwentyOneSlice.block Artifact.allWellFormed 240 7 346 BigC.U.eMulProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e4 := WindowTwentyOneSlice.block Artifact.allWellFormed 247 5 361 BigC.U.e4Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e3 := WindowTwentyOneSlice.block Artifact.allWellFormed 252 5 368 BigC.U.e3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e9 := WindowTwentyOneSlice.block Artifact.allWellFormed 257 9 376 BigC.U.e9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j295 := Artifact.isValidJumpDest_index 191 (by rfl)
      j310 := Artifact.isValidJumpDest_index 203 (by rfl)
      j333 := Artifact.isValidJumpDest_index 217 (by rfl)
      j379 := Artifact.isValidJumpDest_index 247 (by rfl)
      j386 := Artifact.isValidJumpDest_index 252 (by rfl)
      j394 := Artifact.isValidJumpDest_index 257 (by rfl)
      j411 := Artifact.isValidJumpDest_index 266 (by rfl)
      j482 := Artifact.isValidJumpDest_index 317 (by rfl) }

def setupBlocks : BigC.U.SetupBlocks Artifact.submissionArtifact where
  setup := WindowTwentyOneSlice.block Artifact.allWellFormed 148 25 218 BigC.U.setupProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zLoop := WindowTwentyOneSlice.block Artifact.allWellFormed 173 15 253 BigC.U.zLoopProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zExit := WindowTwentyOneSlice.block Artifact.allWellFormed 188 3 272 BigC.U.zExitProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zeroRet := WindowTwentyOneSlice.block Artifact.allWellFormed 191 4 277 BigC.U.zeroRetProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  nz := WindowTwentyOneSlice.block Artifact.allWellFormed 195 8 281 BigC.U.nzProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j236 := Artifact.isValidJumpDest_index 148 (by rfl)
      j271 := Artifact.isValidJumpDest_index 173 (by rfl)
      j295 := Artifact.isValidJumpDest_index 191 (by rfl)
      j299 := Artifact.isValidJumpDest_index 195 (by rfl) }

end Challenge.Modexp.Submission.Proofs.Bytecode.BigC.UBlocks
