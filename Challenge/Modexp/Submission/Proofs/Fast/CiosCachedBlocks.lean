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

def entry : Block Artifact.submissionArtifact .Osaka 4451 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3193 38 4451 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4564 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3231 5 4564 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4569 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3236 3 4569 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4574 (l1Program 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3239 34 4574 (l1Program 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4612 (l1Program 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3273 34 4612 (l1Program 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4650 (l1Program 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3307 34 4650 (l1Program 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4688 (l1Program 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3341 34 4688 (l1Program 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4726 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3375 1 4726 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4727 (l1Program 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3376 34 4727 (l1Program 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4765 (l1Program 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3410 34 4765 (l1Program 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4803 (l1Program 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3444 34 4803 (l1Program 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4841 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3478 33 4841 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4878 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3511 34 4878 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4924 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3545 3 4924 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4929 (l2Program 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3548 32 4929 (l2Program 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4967 (l2Program 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3580 32 4967 (l2Program 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 5005 (l2Program 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3612 32 5005 (l2Program 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5043 (l2Program 96 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3644 32 5043 (l2Program 96 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5081 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3676 1 5081 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5082 (l2Program 64 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3677 32 5082 (l2Program 64 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5120 (l2Program 32 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3709 32 5120 (l2Program 32 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5158
    (l2LastProgram (UInt256.ofNat 8256) (UInt256.ofNat 8288)) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3741 32 5158
    (l2LastProgram (UInt256.ofNat 8256) (UInt256.ofNat 8288))
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5194 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3773 23 5194 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5227 (CiosCached.tailProgram.drop 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3796 8 5227 (CiosCached.tailProgram.drop 23)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4564 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4564 = true :=
  Artifact.isValidJumpDest_index 3231 (by rfl)

theorem jumpDest4726 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4726 = true :=
  Artifact.isValidJumpDest_index 3375 (by rfl)

theorem jumpDest5081 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5081 = true :=
  Artifact.isValidJumpDest_index 3676 (by rfl)

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
