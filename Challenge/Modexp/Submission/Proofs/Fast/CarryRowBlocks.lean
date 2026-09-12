import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyExtra
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-!
# Located blocks of the sqCP1m kernel row (shared by the multiply and the square)

Row head `out` (4037, multiply only), `commonFirst` (4040), the first-loop dispatch
`DUP6 JUMP` (4066); the uniform first-loop blocks live in `KernelChain`; the middle block
with its `JUMPDEST` (4334, the empty-chain entry); the second-loop dispatch `DUP10 JUMP`
(4365) and cells (4367..4622); the tail (4623, ends `DUP3 JUMPI` to the row head `hd`) and
the exit (4649, jumps to the moved CSUB guard 4667).  The kernel `setup` block belongs to
the entry side (`Cios2Dispatch` / `StagedOperandEntry`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowTwentyOneBinding

def out : Block Artifact.submissionArtifact .Osaka 4018 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3027 3 4018 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4047 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3056 2 4047 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4021 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3030 26 4021 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The middle block with its leading `JUMPDEST` (instruction 3295, pc 4334). -/
def mid : Block Artifact.submissionArtifact .Osaka 4315 CarryRowPrograms.middleBlock :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3275 27 4315 CarryRowPrograms.middleBlock
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4346 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3302 2 4346 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The first eight-limb second-loop cell loads its modulus word with `PUSH10 0xc0`. -/
def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4349 (l2Program 10 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3305 30 4349 (l2Program 10 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4394 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3335 30 4394 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4430 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3365 30 4430 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4466 (CiosReadonlyExtra.extraProgram 0 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3395 29 4466 (CiosReadonlyExtra.extraProgram 0 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4500 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3424 1 4500 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4501 (CiosReadonlyExtra.extraProgram 1 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3425 29 4501 (CiosReadonlyExtra.extraProgram 1 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4535 (CiosReadonlyExtra.extraProgram 2 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3454 29 4535 (CiosReadonlyExtra.extraProgram 2 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4569 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3483 30 4569 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4604 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3513 20 4604 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def fullExitProgramPop : List Instr :=
  CiosReadonly.fullExitProgram.dropLast ++ [.op .POP]

def exitBlock : Block Artifact.submissionArtifact .Osaka 4640 fullExitProgramPop :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3539 16 4640 fullExitProgramPop
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4348 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3304 1 4348 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4348 = true :=
  Artifact.isValidJumpDest_index 3304 (by rfl)

/-- The multiply row head (instruction 3040). -/
theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4018 = true :=
  Artifact.isValidJumpDest_index 3027 (by rfl)

/-- The four-limb second-loop entry (instruction 3448). -/
theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4500 = true :=
  Artifact.isValidJumpDest_index 3424 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks
