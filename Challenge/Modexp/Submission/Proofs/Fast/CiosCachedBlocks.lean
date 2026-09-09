import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowTwentyOneBinding

def entry : Block Artifact.submissionArtifact .Osaka 4481 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3200 39 4481 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4595 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3239 7 4595 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4604 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3246 3 4604 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4758 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3389 1 4758 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4902 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3527 44 4902 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4975 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3571 3 4975 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5141 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3722 1 5141 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5262 (CiosCached.tailProgram.take 25) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3831 25 5262 (CiosCached.tailProgram.take 25)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4610 (l1Program 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3249 35 4610 (l1Program 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4647 (l1Program 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3284 35 4647 (l1Program 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4684 (l1Program 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3319 35 4684 (l1Program 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4721 (l1Program 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3354 35 4721 (l1Program 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4759 (l1Program 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3390 35 4759 (l1Program 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4796 (l1Program 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3425 35 4796 (l1Program 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4833 (l1Program 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3460 35 4833 (l1Program 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4870 l1LastProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3495 32 4870 l1LastProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4981 (l2Program 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3574 37 4981 (l2Program 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 5021 (l2Program 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3611 37 5021 (l2Program 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 5061 (l2Program 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3648 37 5061 (l2Program 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5101 (l2Program 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3685 37 5101 (l2Program 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5142 (l2Program 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3723 37 5142 (l2Program 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5182 (l2Program 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3760 37 5182 (l2Program 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5222 l2LastProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3797 34 5222 l2LastProgram
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5298 (CiosCached.tailProgram.drop 25) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3856 8 5298 (CiosCached.tailProgram.drop 25)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4339 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4595 = true :=
  Artifact.isValidJumpDest_index 3239 (by rfl)

theorem jumpDest4502 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4758 = true :=
  Artifact.isValidJumpDest_index 3389 (by rfl)

theorem jumpDest4885 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5141 = true :=
  Artifact.isValidJumpDest_index 3722 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks
