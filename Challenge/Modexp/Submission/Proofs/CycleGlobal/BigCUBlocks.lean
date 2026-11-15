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
  entry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 298 2 447 BigC.Unsigned.entryProgram
    (by change 298+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  init := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 300 4 451 BigC.Unsigned.initProgram
    (by change 300+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  cell := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 304 32 457 BigC.Unsigned.cellProgram
    (by change 304+32 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  guard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 336 3 490 BigC.Unsigned.guardProgram
    (by change 336+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  decide := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 339 3 495 BigC.Unsigned.decideProgram
    (by change 339+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  retry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 342 5 500 BigC.Unsigned.retryProgram
    (by change 342+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  finish := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 347 5 509 BigC.Unsigned.finishProgram
    (by change 347+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumpInit := CycleSubmission.Global.Binding.jumpDest 300 (by rfl)
  jumpLoop := CycleSubmission.Global.Binding.jumpDest 304 (by rfl)
  jumpDone := CycleSubmission.Global.Binding.jumpDest 347 (by rfl)
def mulBlocks : BigC.U.MulBlocks CycleSubmission.Artifact.artifact where
  mEntry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 247 7 376 BigC.U.mEntryProgram
    (by change 247+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 254 8 384 BigC.U.mGuardProgram
    (by change 254+8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mDouble := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 262 4 395 BigC.U.mDoubleProgram
    (by change 262+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 266 16 403 BigC.U.m2Program
    (by change 266+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mAdd := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 282 4 424 BigC.U.mAddProgram
    (by change 282+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 286 5 432 BigC.U.m3Program
    (by change 286+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 291 7 440 BigC.U.m9Program
    (by change 291+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j419 := CycleSubmission.Global.Binding.jumpDest 254 (by rfl)
      j438 := CycleSubmission.Global.Binding.jumpDest 266 (by rfl)
      j467 := CycleSubmission.Global.Binding.jumpDest 286 (by rfl)
      j475 := CycleSubmission.Global.Binding.jumpDest 291 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 298 (by rfl) }
def expBlocks : BigC.U.ExpBlocks CycleSubmission.Artifact.artifact where
  eGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 184 8 275 BigC.U.eGuardProgram
    (by change 184+8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eSquare := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 192 6 286 BigC.U.eSquareProgram
    (by change 192+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 198 23 298 BigC.U.e2Program
    (by change 198+23 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eMul := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 221 7 329 BigC.U.eMulProgram
    (by change 221+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e4 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 228 5 344 BigC.U.e4Program
    (by change 228+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 233 5 351 BigC.U.e3Program
    (by change 233+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 238 9 359 BigC.U.e9Program
    (by change 238+9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j295 := CycleSubmission.Global.Binding.jumpDest 172 (by rfl)
      j310 := CycleSubmission.Global.Binding.jumpDest 184 (by rfl)
      j333 := CycleSubmission.Global.Binding.jumpDest 198 (by rfl)
      j379 := CycleSubmission.Global.Binding.jumpDest 228 (by rfl)
      j386 := CycleSubmission.Global.Binding.jumpDest 233 (by rfl)
      j394 := CycleSubmission.Global.Binding.jumpDest 238 (by rfl)
      j411 := CycleSubmission.Global.Binding.jumpDest 247 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 298 (by rfl) }
def setupBlocks : BigC.U.SetupBlocks CycleSubmission.Artifact.artifact where
  setup := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 130 25 203 BigC.U.setupProgram
    (by change 130+25 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zLoop := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 155 14 238 BigC.U.zLoopProgram
    (by change 155+14 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zExit := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 169 3 255 BigC.U.zExitProgram
    (by change 169+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zeroRet := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 172 4 260 BigC.U.zeroRetProgram
    (by change 172+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  nz := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 176 8 264 BigC.U.nzProgram
    (by change 176+8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j236 := CycleSubmission.Global.Binding.jumpDest 130 (by rfl)
      j271 := CycleSubmission.Global.Binding.jumpDest 155 (by rfl)
      j295 := CycleSubmission.Global.Binding.jumpDest 172 (by rfl)
      j299 := CycleSubmission.Global.Binding.jumpDest 176 (by rfl) }
end CycleSubmission.Global.BigC.UBlocks
