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

def entry : Block Artifact.submissionArtifact .Osaka 4160 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3129 53 4160 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4240 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3182 4 4240 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4244 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3186 2 4244 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4247 (l1FirstProgram 224 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3189 30 4247 (l1FirstProgram 224 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4282 (l1Program 192 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3219 33 4282 (l1Program 192 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4320 (l1Program 160 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3252 33 4320 (l1Program 160 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4358 (l1Program 128 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3285 33 4358 (l1Program 128 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4396 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3318 1 4396 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4397 (l1Program 96 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3319 33 4397 (l1Program 96 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4435 (l1Program 64 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3352 33 4435 (l1Program 64 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4473 (l1Program 32 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3385 33 4473 (l1Program 32 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4511 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3418 31 4511 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4546 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3449 27 4546 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4579 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3476 2 4579 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4582 (l2Program 8 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3479 31 4582 (l2Program 8 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4625 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3510 31 4625 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4661 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3541 31 4661 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4697 (l2Cached96Program 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3572 30 4697 (l2Cached96Program 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4731 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3602 1 4731 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4732 (l2Cached64Program 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3603 30 4732 (l2Cached64Program 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4766 (l2Cached32Program 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3633 30 4766 (l2Cached32Program 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4800 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3663 31 4800 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4835 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3694 23 4835 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4868 (CiosCached.tailProgram.drop 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3717 15 4868 (CiosCached.tailProgram.drop 23)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join8 : Block Artifact.submissionArtifact .Osaka 4246 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3188 1 4246 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL1Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4246 = true :=
  Artifact.isValidJumpDest_index 3188 (by rfl)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4581 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3478 1 4581 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4581 = true :=
  Artifact.isValidJumpDest_index 3478 (by rfl)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4240 = true :=
  Artifact.isValidJumpDest_index 3182 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4396 = true :=
  Artifact.isValidJumpDest_index 3318 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4731 = true :=
  Artifact.isValidJumpDest_index 3602 (by rfl)

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
