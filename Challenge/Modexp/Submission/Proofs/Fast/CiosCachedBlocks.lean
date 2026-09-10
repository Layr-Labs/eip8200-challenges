import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyExtra
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

def entry : Block Artifact.submissionArtifact .Osaka 4160 CiosReadonly.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3129 58 4160 CiosReadonly.fullEntryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4244 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3187 4 4244 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4248 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3191 2 4248 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4251 (l1FirstProgram 224 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3194 30 4251 (l1FirstProgram 224 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4286 (l1Program 192 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3224 33 4286 (l1Program 192 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4324 (l1Program 160 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3257 33 4324 (l1Program 160 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4362 (l1Program 128 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3290 33 4362 (l1Program 128 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4400 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3323 1 4400 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4401 (l1Program 96 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3324 33 4401 (l1Program 96 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4439 (l1Program 64 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3357 33 4439 (l1Program 64 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4477 (l1Program 32 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3390 33 4477 (l1Program 32 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4515 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3423 31 4515 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4550 CiosReadonly.fullMidProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3454 27 4550 CiosReadonly.fullMidProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4583 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3481 2 4583 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4586 (l2Program 10 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3484 31 4586 (l2Program 10 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4631 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3515 31 4631 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4667 (CiosReadonlyExtra.extraProgram 0 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3546 30 4667 (CiosReadonlyExtra.extraProgram 0 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4701 (CiosReadonlyExtra.extraProgram 1 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3576 30 4701 (CiosReadonlyExtra.extraProgram 1 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4735 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3606 1 4735 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4736 (CiosReadonlyExtra.extraProgram 2 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3607 30 4736 (CiosReadonlyExtra.extraProgram 2 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4770 (CiosReadonlyExtra.extraProgram 3 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3637 30 4770 (CiosReadonlyExtra.extraProgram 3 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4804 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3667 31 4804 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4839 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3698 23 4839 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4872 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3721 16 4872 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join8 : Block Artifact.submissionArtifact .Osaka 4250 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3193 1 4250 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL1Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4250 = true :=
  Artifact.isValidJumpDest_index 3193 (by rfl)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4585 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3483 1 4585 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4585 = true :=
  Artifact.isValidJumpDest_index 3483 (by rfl)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4244 = true :=
  Artifact.isValidJumpDest_index 3187 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4400 = true :=
  Artifact.isValidJumpDest_index 3323 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 3606 (by rfl)

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
