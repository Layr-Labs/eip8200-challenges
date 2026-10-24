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
  entry := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 315 2 464 BigC.Unsigned.entryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  init := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 317 4 468 BigC.Unsigned.initProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  cell := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 321 33 474 BigC.Unsigned.cellProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  guard := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 354 3 509 BigC.Unsigned.guardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  decide := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 357 3 514 BigC.Unsigned.decideProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  retry := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 360 5 519 BigC.Unsigned.retryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  finish := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 365 5 528 BigC.Unsigned.finishProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumpInit := CycleSubmission.Global.Binding.jumpDest 317 (by rfl)
  jumpLoop := CycleSubmission.Global.Binding.jumpDest 321 (by rfl)
  jumpDone := CycleSubmission.Global.Binding.jumpDest 365 (by rfl)

def mulBlocks : BigC.U.MulBlocks CycleSubmission.Artifact.artifact where
  mEntry := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 264 7 393 BigC.U.mEntryProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mGuard := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 271 8 401 BigC.U.mGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mDouble := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 279 4 412 BigC.U.mDoubleProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m2 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 283 16 420 BigC.U.m2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  mAdd := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 299 4 441 BigC.U.mAddProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m3 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 303 5 449 BigC.U.m3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  m9 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 308 7 457 BigC.U.m9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j419 := CycleSubmission.Global.Binding.jumpDest 271 (by rfl)
      j438 := CycleSubmission.Global.Binding.jumpDest 283 (by rfl)
      j467 := CycleSubmission.Global.Binding.jumpDest 303 (by rfl)
      j475 := CycleSubmission.Global.Binding.jumpDest 308 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 315 (by rfl) }

def expBlocks : BigC.U.ExpBlocks CycleSubmission.Artifact.artifact where
  eGuard := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 201 8 292 BigC.U.eGuardProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eSquare := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 209 6 303 BigC.U.eSquareProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e2 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 215 23 315 BigC.U.e2Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  eMul := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 238 7 346 BigC.U.eMulProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e4 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 245 5 361 BigC.U.e4Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e3 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 250 5 368 BigC.U.e3Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  e9 := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 255 9 376 BigC.U.e9Program
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j295 := CycleSubmission.Global.Binding.jumpDest 189 (by rfl)
      j310 := CycleSubmission.Global.Binding.jumpDest 201 (by rfl)
      j333 := CycleSubmission.Global.Binding.jumpDest 215 (by rfl)
      j379 := CycleSubmission.Global.Binding.jumpDest 245 (by rfl)
      j386 := CycleSubmission.Global.Binding.jumpDest 250 (by rfl)
      j394 := CycleSubmission.Global.Binding.jumpDest 255 (by rfl)
      j411 := CycleSubmission.Global.Binding.jumpDest 264 (by rfl)
      j482 := CycleSubmission.Global.Binding.jumpDest 315 (by rfl) }

def setupBlocks : BigC.U.SetupBlocks CycleSubmission.Artifact.artifact where
  setup := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 146 25 219 BigC.U.setupProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zLoop := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 171 15 254 BigC.U.zLoopProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zExit := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 186 3 272 BigC.U.zExitProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  zeroRet := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 189 4 277 BigC.U.zeroRetProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  nz := CycleSubmission.Global.Binding.block CycleSubmission.Artifact.wellFormed 193 8 281 BigC.U.nzProgram
    (by decide) (by rw [PCFast.instructionPC_eq_byteLength]; rfl) (by rfl) (by decide)
  jumps :=
    { j236 := CycleSubmission.Global.Binding.jumpDest 146 (by rfl)
      j271 := CycleSubmission.Global.Binding.jumpDest 171 (by rfl)
      j295 := CycleSubmission.Global.Binding.jumpDest 189 (by rfl)
      j299 := CycleSubmission.Global.Binding.jumpDest 193 (by rfl) }

end CycleSubmission.Global.BigC.UBlocks
