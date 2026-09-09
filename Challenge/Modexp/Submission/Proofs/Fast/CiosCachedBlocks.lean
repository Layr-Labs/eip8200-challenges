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

def entry : Block Artifact.submissionArtifact .Osaka 4447 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3189 38 4447 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4560 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3227 5 4560 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4565 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3232 3 4565 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4570 (l1Program 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3235 34 4570 (l1Program 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4608 (l1Program 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3269 34 4608 (l1Program 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4646 (l1Program 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3303 34 4646 (l1Program 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4684 (l1Program 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3337 34 4684 (l1Program 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4722 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3371 1 4722 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4723 (l1Program 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3372 34 4723 (l1Program 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4761 (l1Program 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3406 34 4761 (l1Program 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4799 (l1Program 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3440 34 4799 (l1Program 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4837 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3474 33 4837 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4874 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3507 34 4874 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4920 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3541 3 4920 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4925 (l2Program 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3544 32 4925 (l2Program 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4963 (l2Program 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3576 32 4963 (l2Program 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 5001 (l2Program 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3608 32 5001 (l2Program 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5039 (l2Program 96 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3640 32 5039 (l2Program 96 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5077 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3672 1 5077 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5078 (l2Program 64 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3673 32 5078 (l2Program 64 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5116 (l2Program 32 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3705 32 5116 (l2Program 32 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5154
    (l2LastProgram (UInt256.ofNat 8256) (UInt256.ofNat 8288)) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3737 32 5154
    (l2LastProgram (UInt256.ofNat 8256) (UInt256.ofNat 8288))
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5190 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3769 23 5190 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5223 (CiosCached.tailProgram.drop 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3792 8 5223 (CiosCached.tailProgram.drop 23)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4560 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4560 = true :=
  Artifact.isValidJumpDest_index 3227 (by rfl)

theorem jumpDest4722 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4722 = true :=
  Artifact.isValidJumpDest_index 3371 (by rfl)

theorem jumpDest5077 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5077 = true :=
  Artifact.isValidJumpDest_index 3672 (by rfl)

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
