import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosOperandCache
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

def entry : Block Artifact.submissionArtifact .Osaka 4163 CiosReadonly.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3077 64 4163 CiosReadonly.fullEntryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4252 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3141 3 4252 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4278 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3167 2 4278 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4255 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3144 23 4255 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4281 (CiosOperandCache.wideProgram 192 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3170 33 4281 (CiosOperandCache.wideProgram 192 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4323 (l1Program 160 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3203 33 4323 (l1Program 160 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4361 (l1Program 128 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3236 33 4361 (l1Program 128 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4433 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3299 1 4433 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4399 (CiosOperandCache.extraProgram 0 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3269 30 4399 (CiosOperandCache.extraProgram 0 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4434 (CiosOperandCache.extraProgram 1 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3300 30 4434 (CiosOperandCache.extraProgram 1 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4468 (CiosOperandCache.extraProgram 2 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3330 30 4468 (CiosOperandCache.extraProgram 2 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4502 (l1LastProgram 8256) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3360 31 4502 (l1LastProgram 8256)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4537 CarryRowPrograms.middle :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3391 26 4537 CarryRowPrograms.middle
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4569 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3417 2 4569 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4572 (l2Program 9 192 8448 8480) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3420 31 4572 (l2Program 9 192 8448 8480)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4616 (l2Program 1 160 8416 8448) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3451 31 4616 (l2Program 1 160 8416 8448)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4652 (l2Program 1 128 8384 8416) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3482 31 4652 (l2Program 1 128 8384 8416)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4688 (l2Program 1 96 8352 8384) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3513 31 4688 (l2Program 1 96 8352 8384)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4724 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3544 1 4724 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4725 (l2Program 1 64 8320 8352) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3545 31 4725 (l2Program 1 64 8320 8352)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4761 (l2Program 1 32 8288 8320) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3576 31 4761 (l2Program 1 32 8288 8320)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4797 (l2Program 0 0 8256 8288) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3607 31 4797 (l2Program 0 0 8256 8288)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4832 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3638 20 4832 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4865 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3658 16 4865 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join8 : Block Artifact.submissionArtifact .Osaka 4280 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3169 1 4280 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL1Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4280 = true :=
  Artifact.isValidJumpDest_index 3169 (by rfl)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4571 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3419 1 4571 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4571 = true :=
  Artifact.isValidJumpDest_index 3419 (by rfl)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4252 = true :=
  Artifact.isValidJumpDest_index 3141 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4433 = true :=
  Artifact.isValidJumpDest_index 3299 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4724 = true :=
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
