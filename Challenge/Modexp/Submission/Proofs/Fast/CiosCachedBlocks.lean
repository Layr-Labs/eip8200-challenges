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

def entry : Block Artifact.submissionArtifact .Osaka 4455 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3174 39 4455 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4569 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3213 7 4569 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4578 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3220 3 4578 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4731 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3371 1 4731 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4880 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3520 50 4880 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4948 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3570 3 4948 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5113 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3729 1 5113 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5234 (CiosCached.tailProgram.take 25) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3847 25 5234 (CiosCached.tailProgram.take 25)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4583 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3223 37 4583 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4620 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3260 37 4620 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4657 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3297 37 4657 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4694 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3334 37 4694 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4732 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3372 37 4732 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4769 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3409 37 4769 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4806 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3446 37 4806 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4843 l1Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3483 37 4843 l1Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4953 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3573 39 4953 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4993 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3612 39 4993 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 5033 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3651 39 5033 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5073 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3690 39 5073 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5114 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3730 39 5114 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5154 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3769 39 5154 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5194 l2Program :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3808 39 5194 l2Program
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5269 (CiosCached.tailProgram.drop 25) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3872 8 5269 (CiosCached.tailProgram.drop 25)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4339 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4569 = true :=
  Artifact.isValidJumpDest_index 3213 (by rfl)

theorem jumpDest4502 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4731 = true :=
  Artifact.isValidJumpDest_index 3371 (by rfl)

theorem jumpDest4885 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5113 = true :=
  Artifact.isValidJumpDest_index 3729 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks
