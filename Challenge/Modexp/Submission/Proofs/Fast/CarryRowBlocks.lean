import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedLast
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

Row head `out` (4172, multiply only), `commonFirst` (4175), the first-loop dispatch
`DUP6 JUMP` (4201); the uniform first-loop blocks live in `KernelChain`; the middle block
with its `JUMPDEST` (4469, the empty-chain entry); the second-loop dispatch `DUP10 JUMP`
(4500) and cells (4502..4757); the tail (4758, ends `DUP3 JUMPI` to the row head `hd`) and
the exit (4784, jumps to the moved CSUB guard 4802).  The kernel `setup` block belongs to
the entry side (`Cios2Dispatch` / `StagedOperandEntry`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowTwentyOneBinding

def out : Block Artifact.submissionArtifact .Osaka 4164 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3108 3 4164 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4193 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3137 2 4193 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4167 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3111 26 4167 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The middle block with its leading `JUMPDEST` (instruction 3370, pc 4469). -/
def mid : Block Artifact.submissionArtifact .Osaka 4461 CarryRowPrograms.middleBlock :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3356 27 4461 CarryRowPrograms.middleBlock
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4492 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3383 2 4492 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The first eight-limb second-loop cell loads its modulus word with `PUSH10 0xc0`. -/
def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4495 (l2Program 10 192 4352 4384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3386 30 4495 (l2Program 10 192 4352 4384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4540 (l2Program 1 160 4320 4352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3416 30 4540 (l2Program 1 160 4320 4352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4576 (l2Program 1 128 4288 4320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3446 30 4576 (l2Program 1 128 4288 4320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4612 (CiosReadonlyExtra.extraProgram 0 4256 4288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3476 29 4612 (CiosReadonlyExtra.extraProgram 0 4256 4288)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4646 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3505 1 4646 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4647 (CiosReadonlyExtra.extraProgram 1 4224 4256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3506 29 4647 (CiosReadonlyExtra.extraProgram 1 4224 4256)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4681 (CiosReadonlyExtra.extraProgram 2 4192 4224) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3535 29 4681 (CiosReadonlyExtra.extraProgram 2 4192 4224)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4715 (CiosCachedLast.l2LastProgram 0 0 4160 4192) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3564 30 4715 (CiosCachedLast.l2LastProgram 0 0 4160 4192)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4750 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3594 18 4750 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4786 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3618 18 4786 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4494 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3385 1 4494 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4494 = true :=
  Artifact.isValidJumpDest_index 3385 (by rfl)

/-- The multiply row head (instruction 3115). -/
theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4164 = true :=
  Artifact.isValidJumpDest_index 3108 (by rfl)

/-- The four-limb second-loop entry (instruction 3523). -/
theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4646 = true :=
  Artifact.isValidJumpDest_index 3505 (by rfl)

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
