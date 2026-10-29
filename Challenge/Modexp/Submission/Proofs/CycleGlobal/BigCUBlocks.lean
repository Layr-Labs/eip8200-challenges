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
  entry := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 314 2 464 BigC.Unsigned.entryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  init := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 316 4 468 BigC.Unsigned.initProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  cell := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 320 33 474 BigC.Unsigned.cellProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  guard := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 353 3 509 BigC.Unsigned.guardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  decide := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 356 3 514 BigC.Unsigned.decideProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  retry := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 359 5 519 BigC.Unsigned.retryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  finish := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 364 5 528 BigC.Unsigned.finishProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumpInit := CycleSubmission.Global.Binding.jumpDest 316 (by rfl)
  jumpLoop := CycleSubmission.Global.Binding.jumpDest 320 (by rfl)
  jumpDone := CycleSubmission.Global.Binding.jumpDest 364 (by rfl)

def mulBlocks : BigC.U.MulBlocks CycleSubmission.Artifact.artifact where
  mEntry := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 263 7 393 BigC.U.mEntryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mGuard := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 270 8 401 BigC.U.mGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mDouble := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 278 4 412 BigC.U.mDoubleProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m2 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 282 16 420 BigC.U.m2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mAdd := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 298 4 441 BigC.U.mAddProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m3 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 302 5 449 BigC.U.m3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m9 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 307 7 457 BigC.U.m9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j419 := CycleSubmission.Global.Binding.jumpDest 270 (by rfl)
      j438 := CycleSubmission.Global.Binding.jumpDest 282 (by rfl)
      j467 := CycleSubmission.Global.Binding.jumpDest 302 (by rfl)
      j475 := CycleSubmission.Global.Binding.jumpDest 307 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 314 (by rfl) }

def expBlocks : BigC.U.ExpBlocks CycleSubmission.Artifact.artifact where
  eGuard := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 200 8 292 BigC.U.eGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eSquare := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 208 6 303 BigC.U.eSquareProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e2 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 214 23 315 BigC.U.e2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eMul := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 237 7 346 BigC.U.eMulProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e4 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 244 5 361 BigC.U.e4Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e3 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 249 5 368 BigC.U.e3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e9 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 254 9 376 BigC.U.e9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j295 := CycleSubmission.Global.Binding.jumpDest 188 (by rfl)
      j310 := CycleSubmission.Global.Binding.jumpDest 200 (by rfl)
      j333 := CycleSubmission.Global.Binding.jumpDest 214 (by rfl)
      j379 := CycleSubmission.Global.Binding.jumpDest 244 (by rfl)
      j386 := CycleSubmission.Global.Binding.jumpDest 249 (by rfl)
      j394 := CycleSubmission.Global.Binding.jumpDest 254 (by rfl)
      j411 := CycleSubmission.Global.Binding.jumpDest 263 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 314 (by rfl) }

def setupBlocks : BigC.U.SetupBlocks CycleSubmission.Artifact.artifact where
  setup := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 145 25 219 BigC.U.setupProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zLoop := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 170 15 254 BigC.U.zLoopProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zExit := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 185 3 272 BigC.U.zExitProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zeroRet := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 188 4 277 BigC.U.zeroRetProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  nz := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 192 8 281 BigC.U.nzProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j236 := CycleSubmission.Global.Binding.jumpDest 145 (by rfl)
      j271 := CycleSubmission.Global.Binding.jumpDest 170 (by rfl)
      j295 := CycleSubmission.Global.Binding.jumpDest 188 (by rfl)
      j299 := CycleSubmission.Global.Binding.jumpDest 192 (by rfl) }

end CycleSubmission.Global.BigC.UBlocks
