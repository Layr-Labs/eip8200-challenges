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

Row head `out` (4264, multiply only), `commonFirst` (4267), the first-loop dispatch
`DUP6 JUMP` (4292); the uniform first-loop blocks live in `KernelChain`; the middle block
with its `JUMPDEST` (4553, the empty-chain entry); the second-loop dispatch `DUP10 JUMP`
(4490) and cells (4502..4832); the tail (4833, ends `DUP3 JUMPI` to the row head `hd`) and
the exit (4859, jumps to the moved CSUB guard 4876).  The kernel `setup` block belongs to
the entry side (`Cios2Dispatch` / `StagedOperandEntry`).
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowTwentyOneBinding

def out : Block Artifact.submissionArtifact .Osaka 4256 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3211 3 4256 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4283 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3238 2 4283 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4259 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3214 24 4259 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The middle block with its leading `JUMPDEST` (instruction 3360, pc 4553). -/
def mid : Block Artifact.submissionArtifact .Osaka 4545 CarryRowPrograms.middleBlock :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3458 27 4545 CarryRowPrograms.middleBlock
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4576 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3485 2 4576 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

/-- The first eight-limb second-loop cell loads its modulus word with `PUSH10 0xc0`. -/
def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4579 (l2Program 10 192 4352 4384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3488 30 4579 (l2Program 10 192 4352 4384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4623 (l2Program 1 160 4320 4352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3518 30 4623 (l2Program 1 160 4320 4352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4658 (l2Program 1 128 4288 4320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3548 30 4658 (l2Program 1 128 4288 4320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4693 (CiosReadonlyExtra.extraProgram 0 4256 4288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3578 29 4693 (CiosReadonlyExtra.extraProgram 0 4256 4288)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4726 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3607 1 4726 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4727 (CiosReadonlyExtra.extraProgram 1 4224 4256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3608 29 4727 (CiosReadonlyExtra.extraProgram 1 4224 4256)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4760 (CiosReadonlyExtra.extraProgram 2 4192 4224) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3637 29 4760 (CiosReadonlyExtra.extraProgram 2 4192 4224)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4793 (CiosCachedLast.l2LastProgram 0 0 4160 4192) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3666 30 4793 (CiosCachedLast.l2LastProgram 0 0 4160 4192)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4827 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3696 18 4827 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4861 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3720 14 4861 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4578 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3487 1 4578 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4578 = true :=
  Artifact.isValidJumpDest_index 3487 (by rfl)

/-- The multiply row head (instruction 3110). -/
theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4256 = true :=
  Artifact.isValidJumpDest_index 3211 (by rfl)

/-- The four-limb second-loop entry (instruction 3509). -/
theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4726 = true :=
  Artifact.isValidJumpDest_index 3607 (by rfl)

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
