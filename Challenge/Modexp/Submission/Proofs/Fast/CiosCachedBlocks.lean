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
  WindowTwentyOneSlice.block Artifact.allWellFormed 3180 38 4481 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4595 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3218 5 4595 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4600 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3223 3 4600 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4605 (l1Program 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3226 34 4605 (l1Program 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4643 (l1Program 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3260 34 4643 (l1Program 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4681 (l1Program 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3294 34 4681 (l1Program 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4719 (l1Program 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3328 34 4719 (l1Program 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4757 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3362 1 4757 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4758 (l1Program 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3363 34 4758 (l1Program 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4796 (l1Program 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3397 34 4796 (l1Program 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4834 (l1Program 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3431 34 4834 (l1Program 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4872 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3465 33 4872 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4909 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3498 34 4909 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4955 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3532 3 4955 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4960 (l2Program 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3535 32 4960 (l2Program 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4998 (l2Program 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3567 32 4998 (l2Program 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 5036 (l2Program 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3599 32 5036 (l2Program 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5074 (l2Program 96 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3631 32 5074 (l2Program 96 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5112 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3663 1 5112 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5113 (l2Program 64 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3664 32 5113 (l2Program 64 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5151 (l2Program 32 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3696 32 5151 (l2Program 32 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5189
    (l2LastProgram (UInt256.ofNat 8256) (UInt256.ofNat 8288)) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3728 32 5189
    (l2LastProgram (UInt256.ofNat 8256) (UInt256.ofNat 8288))
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5225 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3760 23 5225 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5258 (CiosCached.tailProgram.drop 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3783 8 5258 (CiosCached.tailProgram.drop 23)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4595 = true :=
  Artifact.isValidJumpDest_index 3218 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4757 = true :=
  Artifact.isValidJumpDest_index 3362 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5112 = true :=
  Artifact.isValidJumpDest_index 3663 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks

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

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedBlocks
