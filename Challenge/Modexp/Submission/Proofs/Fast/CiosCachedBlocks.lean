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
  WindowTwentyOneSlice.block Artifact.allWellFormed 3180 35 4481 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4527 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3215 4 4527 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4531 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3219 3 4531 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4536 (l1FirstProgram 224 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3222 30 4536 (l1FirstProgram 224 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4571 (l1Program 192 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3252 33 4571 (l1Program 192 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4609 (l1Program 160 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3285 33 4609 (l1Program 160 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4647 (l1Program 128 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3318 33 4647 (l1Program 128 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4685 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3351 1 4685 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4686 (l1Program 96 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3352 33 4686 (l1Program 96 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4724 (l1Program 64 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3385 33 4724 (l1Program 64 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4762 (l1Program 32 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3418 33 4762 (l1Program 32 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4800 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3451 31 4800 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4835 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3482 31 4835 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4878 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3513 3 4878 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4883 (l2Program 1 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3516 31 4883 (l2Program 1 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4919 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3547 31 4919 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4955 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3578 31 4955 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4991 (l2Program 1 96 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3609 31 4991 (l2Program 1 96 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5027 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3640 1 5027 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5028 (l2Program 1 64 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3641 31 5028 (l2Program 1 64 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5064 (l2Program 1 32 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3672 31 5064 (l2Program 1 32 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5100 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3703 31 5100 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5135 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3734 23 5135 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5168 (CiosCached.tailProgram.drop 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3757 8 5168 (CiosCached.tailProgram.drop 23)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4527 = true :=
  Artifact.isValidJumpDest_index 3215 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4685 = true :=
  Artifact.isValidJumpDest_index 3351 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5027 = true :=
  Artifact.isValidJumpDest_index 3640 (by rfl)

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
