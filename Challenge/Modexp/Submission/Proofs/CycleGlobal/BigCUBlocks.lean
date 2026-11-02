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
  entry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 311 2 464 BigC.Unsigned.entryProgram
    (by change 311 + 2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  init := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 313 4 468 BigC.Unsigned.initProgram
    (by change 313 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  cell := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 317 33 474 BigC.Unsigned.cellProgram
    (by change 317 + 33 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  guard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 350 3 509 BigC.Unsigned.guardProgram
    (by change 350 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  decide := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 353 3 514 BigC.Unsigned.decideProgram
    (by change 353 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  retry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 356 5 519 BigC.Unsigned.retryProgram
    (by change 356 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  finish := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 361 5 528 BigC.Unsigned.finishProgram
    (by change 361 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumpInit := CycleSubmission.Global.Binding.jumpDest 313 (by rfl)
  jumpLoop := CycleSubmission.Global.Binding.jumpDest 317 (by rfl)
  jumpDone := CycleSubmission.Global.Binding.jumpDest 361 (by rfl)

def mulBlocks : BigC.U.MulBlocks CycleSubmission.Artifact.artifact where
  mEntry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 260 7 393 BigC.U.mEntryProgram
    (by change 260 + 7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 267 8 401 BigC.U.mGuardProgram
    (by change 267 + 8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mDouble := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 275 4 412 BigC.U.mDoubleProgram
    (by change 275 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 279 16 420 BigC.U.m2Program
    (by change 279 + 16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mAdd := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 295 4 441 BigC.U.mAddProgram
    (by change 295 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 299 5 449 BigC.U.m3Program
    (by change 299 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 304 7 457 BigC.U.m9Program
    (by change 304 + 7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j419 := CycleSubmission.Global.Binding.jumpDest 267 (by rfl)
      j438 := CycleSubmission.Global.Binding.jumpDest 279 (by rfl)
      j467 := CycleSubmission.Global.Binding.jumpDest 299 (by rfl)
      j475 := CycleSubmission.Global.Binding.jumpDest 304 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 311 (by rfl) }

def expBlocks : BigC.U.ExpBlocks CycleSubmission.Artifact.artifact where
  eGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 197 8 292 BigC.U.eGuardProgram
    (by change 197 + 8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eSquare := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 205 6 303 BigC.U.eSquareProgram
    (by change 205 + 6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 211 23 315 BigC.U.e2Program
    (by change 211 + 23 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eMul := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 234 7 346 BigC.U.eMulProgram
    (by change 234 + 7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e4 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 241 5 361 BigC.U.e4Program
    (by change 241 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 246 5 368 BigC.U.e3Program
    (by change 246 + 5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 251 9 376 BigC.U.e9Program
    (by change 251 + 9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j295 := CycleSubmission.Global.Binding.jumpDest 185 (by rfl)
      j310 := CycleSubmission.Global.Binding.jumpDest 197 (by rfl)
      j333 := CycleSubmission.Global.Binding.jumpDest 211 (by rfl)
      j379 := CycleSubmission.Global.Binding.jumpDest 241 (by rfl)
      j386 := CycleSubmission.Global.Binding.jumpDest 246 (by rfl)
      j394 := CycleSubmission.Global.Binding.jumpDest 251 (by rfl)
      j411 := CycleSubmission.Global.Binding.jumpDest 260 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 311 (by rfl) }

def setupBlocks : BigC.U.SetupBlocks CycleSubmission.Artifact.artifact where
  setup := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 143 25 219 BigC.U.setupProgram
    (by change 143 + 25 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zLoop := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 168 14 254 BigC.U.zLoopProgram
    (by change 168 + 14 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zExit := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 182 3 272 BigC.U.zExitProgram
    (by change 182 + 3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zeroRet := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 185 4 277 BigC.U.zeroRetProgram
    (by change 185 + 4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  nz := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 189 8 281 BigC.U.nzProgram
    (by change 189 + 8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j236 := CycleSubmission.Global.Binding.jumpDest 143 (by rfl)
      j271 := CycleSubmission.Global.Binding.jumpDest 168 (by rfl)
      j295 := CycleSubmission.Global.Binding.jumpDest 185 (by rfl)
      j299 := CycleSubmission.Global.Binding.jumpDest 189 (by rfl) }

end CycleSubmission.Global.BigC.UBlocks
