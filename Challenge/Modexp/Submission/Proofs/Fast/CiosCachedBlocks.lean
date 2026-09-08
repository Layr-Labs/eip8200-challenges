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
  WindowTwentyOneSlice.block Artifact.allWellFormed 3246 4 4604 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4758 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3398 1 4758 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4907 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3547 50 4907 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4975 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3597 4 4975 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5141 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3757 1 5141 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5262 (CiosCached.tailProgram.take 26) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3875 26 5262 (CiosCached.tailProgram.take 26)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4610 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3250 37 4610 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4647 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3287 37 4647 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4684 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3324 37 4684 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4721 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3361 37 4721 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4759 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3399 37 4759 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4796 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3436 37 4796 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4833 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3473 37 4833 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4870 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3510 37 4870 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4981 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3601 39 4981 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 5021 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3640 39 5021 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 5061 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3679 39 5061 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5101 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3718 39 5101 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5142 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3758 39 5142 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5182 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3797 39 5182 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5222 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3836 39 5222 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5298 (CiosCached.tailProgram.drop 26) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3901 8 5298 (CiosCached.tailProgram.drop 26)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4339 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4595 = true :=
  Artifact.isValidJumpDest_index 3239 (by rfl)

theorem jumpDest4502 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4758 = true :=
  Artifact.isValidJumpDest_index 3398 (by rfl)

theorem jumpDest4885 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5141 = true :=
  Artifact.isValidJumpDest_index 3757 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks
