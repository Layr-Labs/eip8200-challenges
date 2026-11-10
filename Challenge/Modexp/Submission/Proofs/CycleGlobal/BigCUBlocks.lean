import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUnsignedGas
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUMul
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUExpRun
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUSetupRun

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

/-! Location certificates binding the generic big-modulus ADDM / MULM proofs to the submitted artifact. -/

namespace CycleSubmission.Global.BigC.UBlocks
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding

def unsignedBlocks : BigC.Unsigned.Blocks CycleSubmission.Artifact.artifact where
  entry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 303 2 451 BigC.Unsigned.entryProgram
    (by change 303 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  init := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 305 4 455 BigC.Unsigned.initProgram
    (by change 305 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  cell := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 309 33 461 BigC.Unsigned.cellProgram
    (by change 309 + 33 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  guard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 342 3 495 BigC.Unsigned.guardProgram
    (by change 342 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  decide := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 345 3 500 BigC.Unsigned.decideProgram
    (by change 345 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  retry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 348 5 505 BigC.Unsigned.retryProgram
    (by change 348 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  finish := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 353 5 514 BigC.Unsigned.finishProgram
    (by change 353 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumpInit := CycleSubmission.Global.Binding.jumpDest 305 (by rfl)
  jumpLoop := CycleSubmission.Global.Binding.jumpDest 309 (by rfl)
  jumpDone := CycleSubmission.Global.Binding.jumpDest 353 (by rfl)

def mulBlocks : BigC.U.MulBlocks CycleSubmission.Artifact.artifact where
  mEntry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 252 7 380 BigC.U.mEntryProgram
    (by change 252 + 7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 259 8 388 BigC.U.mGuardProgram
    (by change 259 + 8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mDouble := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 267 4 399 BigC.U.mDoubleProgram
    (by change 267 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 271 16 407 BigC.U.m2Program
    (by change 271 + 16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mAdd := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 287 4 428 BigC.U.mAddProgram
    (by change 287 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 291 5 436 BigC.U.m3Program
    (by change 291 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 296 7 444 BigC.U.m9Program
    (by change 296 + 7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j419 := CycleSubmission.Global.Binding.jumpDest 259 (by rfl)
      j438 := CycleSubmission.Global.Binding.jumpDest 271 (by rfl)
      j467 := CycleSubmission.Global.Binding.jumpDest 291 (by rfl)
      j475 := CycleSubmission.Global.Binding.jumpDest 296 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 303 (by rfl) }

def expBlocks : BigC.U.ExpBlocks CycleSubmission.Artifact.artifact where
  eGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 189 8 279 BigC.U.eGuardProgram
    (by change 189 + 8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eSquare := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 197 6 290 BigC.U.eSquareProgram
    (by change 197 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 203 23 302 BigC.U.e2Program
    (by change 203 + 23 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eMul := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 226 7 333 BigC.U.eMulProgram
    (by change 226 + 7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e4 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 233 5 348 BigC.U.e4Program
    (by change 233 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 238 5 355 BigC.U.e3Program
    (by change 238 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 243 9 363 BigC.U.e9Program
    (by change 243 + 9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j295 := CycleSubmission.Global.Binding.jumpDest 177 (by rfl)
      j310 := CycleSubmission.Global.Binding.jumpDest 189 (by rfl)
      j333 := CycleSubmission.Global.Binding.jumpDest 203 (by rfl)
      j379 := CycleSubmission.Global.Binding.jumpDest 233 (by rfl)
      j386 := CycleSubmission.Global.Binding.jumpDest 238 (by rfl)
      j394 := CycleSubmission.Global.Binding.jumpDest 243 (by rfl)
      j411 := CycleSubmission.Global.Binding.jumpDest 252 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 303 (by rfl) }

def setupBlocks : BigC.U.SetupBlocks CycleSubmission.Artifact.artifact where
  setup := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 135 25 207 BigC.U.setupProgram
    (by change 135 + 25 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zLoop := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 160 14 242 BigC.U.zLoopProgram
    (by change 160 + 14 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zExit := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 174 3 259 BigC.U.zExitProgram
    (by change 174 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zeroRet := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 177 4 264 BigC.U.zeroRetProgram
    (by change 177 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  nz := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 181 8 268 BigC.U.nzProgram
    (by change 181 + 8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j236 := CycleSubmission.Global.Binding.jumpDest 135 (by rfl)
      j271 := CycleSubmission.Global.Binding.jumpDest 160 (by rfl)
      j295 := CycleSubmission.Global.Binding.jumpDest 177 (by rfl)
      j299 := CycleSubmission.Global.Binding.jumpDest 181 (by rfl) }

end CycleSubmission.Global.BigC.UBlocks
