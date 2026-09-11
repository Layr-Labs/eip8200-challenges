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

def entry : Block Artifact.submissionArtifact .Osaka 4072 CiosReadonly.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3044 57 4072 CiosReadonly.fullEntryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4164 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3101 3 4164 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4193 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3130 2 4193 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4167 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3104 26 4167 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4282 (l1Program 192 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3133 33 4282 (l1Program 192 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4320 (l1Program 160 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3169 33 4320 (l1Program 160 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4358 (l1Program 128 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3232 33 4358 (l1Program 128 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4347 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3298 1 4347 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4396 (l1Program 96 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3265 33 4396 (l1Program 96 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4435 (l1Program 64 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3299 33 4435 (l1Program 64 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4473 (l1Program 32 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3332 33 4473 (l1Program 32 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4511 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3365 31 4511 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4461 CiosReadonly.fullMidProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3396 26 4461 CiosReadonly.fullMidProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4507 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3422 2 4507 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4510 (l2Program 11 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3425 31 4510 (l2Program 11 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4555 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3445 31 4555 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4591 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3476 31 4591 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4627 (CiosReadonlyExtra.extraProgram 0 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3507 30 4627 (CiosReadonlyExtra.extraProgram 0 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4661 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3537 1 4661 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4662 (CiosReadonlyExtra.extraProgram 1 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3538 30 4662 (CiosReadonlyExtra.extraProgram 1 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4696 (CiosReadonlyExtra.extraProgram 2 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3568 30 4696 (CiosReadonlyExtra.extraProgram 2 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4730 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3598 31 4730 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4765 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3629 23 4765 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4794 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3652 16 4794 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join8 : Block Artifact.submissionArtifact .Osaka 4195 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3132 1 4195 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL1Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4195 = true :=
  Artifact.isValidJumpDest_index 3132 (by rfl)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4509 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3424 1 4509 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4509 = true :=
  Artifact.isValidJumpDest_index 3424 (by rfl)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4164 = true :=
  Artifact.isValidJumpDest_index 3101 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4347 = true :=
  Artifact.isValidJumpDest_index 3298 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4661 = true :=
  Artifact.isValidJumpDest_index 3537 (by rfl)

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
