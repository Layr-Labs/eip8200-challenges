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
  entry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 299 2 416 BigC.Unsigned.entryProgram
    (by change 299+2 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  init := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 301 4 420 BigC.Unsigned.initProgram
    (by change 301+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  cell := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 305 32 426 BigC.Unsigned.cellProgram
    (by change 305+32 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  guard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 337 3 459 BigC.Unsigned.guardProgram
    (by change 337+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  decide := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 340 3 464 BigC.Unsigned.decideProgram
    (by change 340+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  retry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 343 5 469 BigC.Unsigned.retryProgram
    (by change 343+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  finish := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 348 5 478 BigC.Unsigned.finishProgram
    (by change 348+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumpInit := CycleSubmission.Global.Binding.jumpDest 301 (by rfl)
  jumpLoop := CycleSubmission.Global.Binding.jumpDest 305 (by rfl)
  jumpDone := CycleSubmission.Global.Binding.jumpDest 348 (by rfl)
def mulBlocks : BigC.U.MulBlocks CycleSubmission.Artifact.artifact where
  mEntry := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 248 7 345 BigC.U.mEntryProgram
    (by change 248+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 255 8 353 BigC.U.mGuardProgram
    (by change 255+8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mDouble := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 263 4 364 BigC.U.mDoubleProgram
    (by change 263+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 267 16 372 BigC.U.m2Program
    (by change 267+16 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  mAdd := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 283 4 393 BigC.U.mAddProgram
    (by change 283+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 287 5 401 BigC.U.m3Program
    (by change 287+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  m9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 292 7 409 BigC.U.m9Program
    (by change 292+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j419 := CycleSubmission.Global.Binding.jumpDest 255 (by rfl)
      j438 := CycleSubmission.Global.Binding.jumpDest 267 (by rfl)
      j467 := CycleSubmission.Global.Binding.jumpDest 287 (by rfl)
      j475 := CycleSubmission.Global.Binding.jumpDest 292 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 299 (by rfl) }
def expBlocks : BigC.U.ExpBlocks CycleSubmission.Artifact.artifact where
  eGuard := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 185 8 244 BigC.U.eGuardProgram
    (by change 185+8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eSquare := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 193 6 255 BigC.U.eSquareProgram
    (by change 193+6 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e2 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 199 23 267 BigC.U.e2Program
    (by change 199+23 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  eMul := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 222 7 298 BigC.U.eMulProgram
    (by change 222+7 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e4 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 229 5 313 BigC.U.e4Program
    (by change 229+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e3 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 234 5 320 BigC.U.e3Program
    (by change 234+5 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  e9 := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 239 9 328 BigC.U.e9Program
    (by change 239+9 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j295 := CycleSubmission.Global.Binding.jumpDest 173 (by rfl)
      j310 := CycleSubmission.Global.Binding.jumpDest 185 (by rfl)
      j333 := CycleSubmission.Global.Binding.jumpDest 199 (by rfl)
      j379 := CycleSubmission.Global.Binding.jumpDest 229 (by rfl)
      j386 := CycleSubmission.Global.Binding.jumpDest 234 (by rfl)
      j394 := CycleSubmission.Global.Binding.jumpDest 239 (by rfl)
      j411 := CycleSubmission.Global.Binding.jumpDest 248 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 299 (by rfl) }
def setupBlocks : BigC.U.SetupBlocks CycleSubmission.Artifact.artifact where
  setup := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 131 25 172 BigC.U.setupProgram
    (by change 131+25 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zLoop := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 156 14 207 BigC.U.zLoopProgram
    (by change 156+14 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zExit := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 170 3 224 BigC.U.zExitProgram
    (by change 170+3 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  zeroRet := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 173 4 229 BigC.U.zeroRetProgram
    (by change 173+4 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  nz := WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 177 8 233 BigC.U.nzProgram
    (by change 177+8 ≤ CycleSubmission.Artifact.instructions.length; rw [CycleSubmission.Artifact.instructionCount]; decide)
    (by rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]; rfl)
    (by rw [Challenge.Modexp.Submission.Proofs.Fast.CRTSliceFast.locations_map]; rfl)
    (by decide)
  jumps :=
    { j236 := CycleSubmission.Global.Binding.jumpDest 131 (by rfl)
      j271 := CycleSubmission.Global.Binding.jumpDest 156 (by rfl)
      j295 := CycleSubmission.Global.Binding.jumpDest 173 (by rfl)
      j299 := CycleSubmission.Global.Binding.jumpDest 177 (by rfl) }
end CycleSubmission.Global.BigC.UBlocks
