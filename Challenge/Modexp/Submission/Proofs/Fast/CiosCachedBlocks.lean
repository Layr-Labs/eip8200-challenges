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
  WindowTwentyOneSlice.block Artifact.allWellFormed 3129 57 4160 CiosReadonly.fullEntryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4247 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3186 3 4247 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4276 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3215 2 4276 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4250 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3189 26 4250 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4279 (l1Program 192 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3218 33 4279 (l1Program 192 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4317 (l1Program 160 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3251 33 4317 (l1Program 160 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4355 (l1Program 128 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3284 33 4355 (l1Program 128 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4431 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3350 1 4431 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4393 (l1Program 96 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3317 33 4393 (l1Program 96 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4432 (l1Program 64 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3351 33 4432 (l1Program 64 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4470 (l1Program 32 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3384 33 4470 (l1Program 32 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4508 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3417 31 4508 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4543 CiosReadonly.fullMidProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3448 27 4543 CiosReadonly.fullMidProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4576 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3475 2 4576 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4579 (l2Program 11 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3478 31 4579 (l2Program 11 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4625 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3509 31 4625 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4661 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3540 31 4661 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4697 (CiosReadonlyExtra.extraProgram 0 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3571 30 4697 (CiosReadonlyExtra.extraProgram 0 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4731 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3601 1 4731 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4732 (CiosReadonlyExtra.extraProgram 1 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3602 30 4732 (CiosReadonlyExtra.extraProgram 1 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4766 (CiosReadonlyExtra.extraProgram 2 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3632 30 4766 (CiosReadonlyExtra.extraProgram 2 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4800 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3662 31 4800 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4835 (CiosCached.tailProgram.take 23) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3693 23 4835 (CiosCached.tailProgram.take 23)
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4868 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3716 16 4868 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join8 : Block Artifact.submissionArtifact .Osaka 4278 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3217 1 4278 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL1Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4278 = true :=
  Artifact.isValidJumpDest_index 3217 (by rfl)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4578 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3477 1 4578 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4578 = true :=
  Artifact.isValidJumpDest_index 3477 (by rfl)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4247 = true :=
  Artifact.isValidJumpDest_index 3186 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4431 = true :=
  Artifact.isValidJumpDest_index 3350 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4731 = true :=
  Artifact.isValidJumpDest_index 3601 (by rfl)

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
