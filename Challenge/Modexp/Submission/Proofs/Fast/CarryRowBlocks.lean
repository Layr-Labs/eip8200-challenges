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

Row head `out` (4260, multiply only), `commonFirst` (4263), the first-loop dispatch
`DUP6 JUMP` (4289); the uniform first-loop blocks live in `KernelChain`; the middle block
with its `JUMPDEST` (4550, the empty-chain entry); the second-loop dispatch `DUP10 JUMP`
(4447) and cells (4449..4831); the tail (4832, ends `DUP3 JUMPI` to the row head `hd`) and
the exit (4858, jumps to the moved CSUB guard 4874).  The kernel `setup` block belongs to
the entry side (`Cios2Dispatch` / `StagedOperandEntry`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowTwentyOneBinding

def out : Block Artifact.submissionArtifact .Osaka 4252 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3228 3 4252 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4281 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3257 2 4281 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4255 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3231 26 4255 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The middle block with its leading `JUMPDEST` (instruction 3412, pc 4550). -/
def mid : Block Artifact.submissionArtifact .Osaka 4542 CarryRowPrograms.middleBlock :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3476 27 4542 CarryRowPrograms.middleBlock
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4573 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3503 2 4573 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The first eight-limb second-loop cell loads its modulus word with `PUSH10 0xc0`. -/
def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4576 (l2Program 10 192 4352 4384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3506 30 4576 (l2Program 10 192 4352 4384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4620 (l2Program 1 160 4320 4352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3536 30 4620 (l2Program 1 160 4320 4352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4655 (l2Program 1 128 4288 4320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3566 30 4655 (l2Program 1 128 4288 4320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4690 (CiosReadonlyExtra.extraProgram 0 4256 4288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3596 29 4690 (CiosReadonlyExtra.extraProgram 0 4256 4288)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4723 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3625 1 4723 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4724 (CiosReadonlyExtra.extraProgram 1 4224 4256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3626 29 4724 (CiosReadonlyExtra.extraProgram 1 4224 4256)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4757 (CiosReadonlyExtra.extraProgram 2 4192 4224) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3655 29 4757 (CiosReadonlyExtra.extraProgram 2 4192 4224)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4790 (CiosCachedLast.l2LastProgram 0 0 4160 4192) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3684 30 4790 (CiosCachedLast.l2LastProgram 0 0 4160 4192)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4824 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3714 18 4824 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4860 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3738 14 4860 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4575 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3505 1 4575 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4575 = true :=
  Artifact.isValidJumpDest_index 3505 (by rfl)

/-- The multiply row head (instruction 3040). -/
theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4252 = true :=
  Artifact.isValidJumpDest_index 3228 (by rfl)

/-- The four-limb second-loop entry (instruction 3565). -/
theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4723 = true :=
  Artifact.isValidJumpDest_index 3625 (by rfl)

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
