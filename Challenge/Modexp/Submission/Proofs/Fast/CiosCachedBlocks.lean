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

def entry : Block Artifact.submissionArtifact .Osaka 4076 CiosReadonly.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3047 57 4076 CiosReadonly.fullEntryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4173 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3104 3 4173 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4202 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3137 2 4202 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4176 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3105 26 4176 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4291 (l1Program 192 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3140 33 4291 (l1Program 192 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4329 (l1Program 160 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3176 33 4329 (l1Program 160 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4367 (l1Program 128 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3239 33 4367 (l1Program 128 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4356 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3305 1 4356 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4405 (l1Program 96 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3272 33 4405 (l1Program 96 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4444 (l1Program 64 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3306 33 4444 (l1Program 64 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4482 (l1Program 32 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3339 33 4482 (l1Program 32 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4511 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3372 31 4511 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4470 CiosReadonly.fullMidProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3403 26 4470 CiosReadonly.fullMidProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4516 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3429 2 4516 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4519 (l2Program 11 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3432 31 4519 (l2Program 11 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4555 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3452 31 4555 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4591 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3483 31 4591 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4627 (CiosReadonlyExtra.extraProgram 0 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3514 30 4627 (CiosReadonlyExtra.extraProgram 0 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4661 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3544 1 4661 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4662 (CiosReadonlyExtra.extraProgram 1 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3545 30 4662 (CiosReadonlyExtra.extraProgram 1 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4696 (CiosReadonlyExtra.extraProgram 2 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3575 30 4696 (CiosReadonlyExtra.extraProgram 2 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4730 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3605 31 4730 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4765 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3636 23 4765 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4794 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3659 16 4794 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join8 : Block Artifact.submissionArtifact .Osaka 4204 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3139 1 4204 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL1Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4204 = true :=
  Artifact.isValidJumpDest_index 3139 (by rfl)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4518 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3431 1 4518 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4518 = true :=
  Artifact.isValidJumpDest_index 3431 (by rfl)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4173 = true :=
  Artifact.isValidJumpDest_index 3104 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4356 = true :=
  Artifact.isValidJumpDest_index 3305 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4661 = true :=
  Artifact.isValidJumpDest_index 3544 (by rfl)

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
