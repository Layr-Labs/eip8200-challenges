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

def entry : Block Artifact.submissionArtifact .Osaka 4488 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3193 35 4488 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4534 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3228 4 4534 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4538 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3232 3 4538 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4543 (l1FirstProgram 224 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3235 30 4543 (l1FirstProgram 224 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4578 (l1Program 192 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3265 33 4578 (l1Program 192 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4616 (l1Program 160 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3298 33 4616 (l1Program 160 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4654 (l1Program 128 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3331 33 4654 (l1Program 128 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4692 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3364 1 4692 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4693 (l1Program 96 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3365 33 4693 (l1Program 96 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4731 (l1Program 64 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3398 33 4731 (l1Program 64 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4769 (l1Program 32 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3431 33 4769 (l1Program 32 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4807 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3464 31 4807 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4842 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3495 31 4842 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4885 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3526 3 4885 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4890 (l2Program 1 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3529 31 4890 (l2Program 1 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4926 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3560 31 4926 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4962 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3591 31 4962 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4998 (l2Program 1 96 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3622 31 4998 (l2Program 1 96 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5034 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3653 1 5034 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5035 (l2Program 1 64 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3654 31 5035 (l2Program 1 64 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5071 (l2Program 1 32 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3685 31 5071 (l2Program 1 32 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5107 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3716 31 5107 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5142 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3747 23 5142 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5175 (CiosCached.tailProgram.drop 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3770 8 5175 (CiosCached.tailProgram.drop 23)
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4534 = true :=
  Artifact.isValidJumpDest_index 3228 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4692 = true :=
  Artifact.isValidJumpDest_index 3364 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5034 = true :=
  Artifact.isValidJumpDest_index 3653 (by rfl)

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
