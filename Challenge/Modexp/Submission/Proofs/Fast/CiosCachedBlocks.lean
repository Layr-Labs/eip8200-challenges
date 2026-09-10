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
  WindowTwentyOneSlice.block Artifact.allWellFormed 3180 42 4481 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4540 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3222 4 4540 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4544 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3226 2 4544 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4547 (l1FirstProgram 224 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3229 30 4547 (l1FirstProgram 224 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4582 (l1Program 192 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3259 33 4582 (l1Program 192 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4620 (l1Program 160 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3292 33 4620 (l1Program 160 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4658 (l1Program 128 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3325 33 4658 (l1Program 128 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4696 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3358 1 4696 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4697 (l1Program 96 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3359 33 4697 (l1Program 96 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4735 (l1Program 64 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3392 33 4735 (l1Program 64 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4773 (l1Program 32 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3425 33 4773 (l1Program 32 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4811 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3458 31 4811 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4846 midProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3489 31 4846 midProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4889 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3520 2 4889 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4892 (l2Program 1 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3523 31 4892 (l2Program 1 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4928 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3554 31 4928 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4964 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3585 31 4964 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5000 (l2Program 1 96 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3616 31 5000 (l2Program 1 96 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5036 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3647 1 5036 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5037 (l2Program 1 64 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3648 31 5037 (l2Program 1 64 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5073 (l2Program 1 32 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3679 31 5073 (l2Program 1 32 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5109 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3710 31 5109 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 5144 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3741 23 5144 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 5177 (CiosCached.tailProgram.drop 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3764 9 5177 (CiosCached.tailProgram.drop 23)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join8 : Block Artifact.submissionArtifact .Osaka 4546 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3228 1 4546 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL1Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4546 = true :=
  Artifact.isValidJumpDest_index 3228 (by rfl)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4891 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3522 1 4891 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4891 = true :=
  Artifact.isValidJumpDest_index 3522 (by rfl)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4540 = true :=
  Artifact.isValidJumpDest_index 3222 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4696 = true :=
  Artifact.isValidJumpDest_index 3358 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5036 = true :=
  Artifact.isValidJumpDest_index 3647 (by rfl)

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
