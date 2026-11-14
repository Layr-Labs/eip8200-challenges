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
  entry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 302 2 451 BigC.Unsigned.entryProgram
    (by change 302+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  init := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 304 4 455 BigC.Unsigned.initProgram
    (by change 304+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  cell := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 308 33 461 BigC.Unsigned.cellProgram
    (by change 308+33 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  guard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 341 3 495 BigC.Unsigned.guardProgram
    (by change 341+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  decide := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 344 3 500 BigC.Unsigned.decideProgram
    (by change 344+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  retry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 347 5 505 BigC.Unsigned.retryProgram
    (by change 347+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  finish := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 352 5 514 BigC.Unsigned.finishProgram
    (by change 352+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumpInit := CycleSubmission.Global.Binding.jumpDest 304 (by rfl)
  jumpLoop := CycleSubmission.Global.Binding.jumpDest 308 (by rfl)
  jumpDone := CycleSubmission.Global.Binding.jumpDest 352 (by rfl)
def mulBlocks : BigC.U.MulBlocks CycleSubmission.Artifact.artifact where
  mEntry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 251 7 380 BigC.U.mEntryProgram
    (by change 251+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 258 8 388 BigC.U.mGuardProgram
    (by change 258+8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mDouble := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 266 4 399 BigC.U.mDoubleProgram
    (by change 266+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 270 16 407 BigC.U.m2Program
    (by change 270+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mAdd := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 286 4 428 BigC.U.mAddProgram
    (by change 286+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 290 5 436 BigC.U.m3Program
    (by change 290+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 295 7 444 BigC.U.m9Program
    (by change 295+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j419 := CycleSubmission.Global.Binding.jumpDest 258 (by rfl)
      j438 := CycleSubmission.Global.Binding.jumpDest 270 (by rfl)
      j467 := CycleSubmission.Global.Binding.jumpDest 290 (by rfl)
      j475 := CycleSubmission.Global.Binding.jumpDest 295 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 302 (by rfl) }
def expBlocks : BigC.U.ExpBlocks CycleSubmission.Artifact.artifact where
  eGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 188 8 279 BigC.U.eGuardProgram
    (by change 188+8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eSquare := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 196 6 290 BigC.U.eSquareProgram
    (by change 196+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 202 23 302 BigC.U.e2Program
    (by change 202+23 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eMul := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 225 7 333 BigC.U.eMulProgram
    (by change 225+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e4 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 232 5 348 BigC.U.e4Program
    (by change 232+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 237 5 355 BigC.U.e3Program
    (by change 237+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 242 9 363 BigC.U.e9Program
    (by change 242+9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j295 := CycleSubmission.Global.Binding.jumpDest 176 (by rfl)
      j310 := CycleSubmission.Global.Binding.jumpDest 188 (by rfl)
      j333 := CycleSubmission.Global.Binding.jumpDest 202 (by rfl)
      j379 := CycleSubmission.Global.Binding.jumpDest 232 (by rfl)
      j386 := CycleSubmission.Global.Binding.jumpDest 237 (by rfl)
      j394 := CycleSubmission.Global.Binding.jumpDest 242 (by rfl)
      j411 := CycleSubmission.Global.Binding.jumpDest 251 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 302 (by rfl) }
def setupBlocks : BigC.U.SetupBlocks CycleSubmission.Artifact.artifact where
  setup := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 134 25 207 BigC.U.setupProgram
    (by change 134+25 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zLoop := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 159 14 242 BigC.U.zLoopProgram
    (by change 159+14 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zExit := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 173 3 259 BigC.U.zExitProgram
    (by change 173+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zeroRet := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 176 4 264 BigC.U.zeroRetProgram
    (by change 176+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  nz := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 180 8 268 BigC.U.nzProgram
    (by change 180+8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j236 := CycleSubmission.Global.Binding.jumpDest 134 (by rfl)
      j271 := CycleSubmission.Global.Binding.jumpDest 159 (by rfl)
      j295 := CycleSubmission.Global.Binding.jumpDest 176 (by rfl)
      j299 := CycleSubmission.Global.Binding.jumpDest 180 (by rfl) }
end CycleSubmission.Global.BigC.UBlocks
