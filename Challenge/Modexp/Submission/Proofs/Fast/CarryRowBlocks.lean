import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandEntry
import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandL1
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyPrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosReadonlyExtra
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel

open CiosCached WindowTwentyOneBinding

def entry : Block Artifact.submissionArtifact .Osaka 4076 StagedOperand.fullEntryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3085 60 4076 StagedOperand.fullEntryProgram
    (by decide) (by decide) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4169 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3148 3 4169 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4198 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3177 2 4198 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4172 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3151 26 4172 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4200 (StagedOperand.l1Program 192 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3179 31 4200 (StagedOperand.l1Program 192 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4238 (StagedOperand.l1Program 160 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3210 31 4238 (StagedOperand.l1Program 160 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4276 (StagedOperand.l1Program 128 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3241 31 4276 (StagedOperand.l1Program 128 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4352 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3303 1 4352 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4314 (StagedOperand.l1Program 96 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3272 31 4314 (StagedOperand.l1Program 96 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4352 (StagedOperand.l1Program 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3303 31 4352 (StagedOperand.l1Program 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4390 (StagedOperand.l1Program 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3334 31 4390 (StagedOperand.l1Program 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4428 (StagedOperand.l1Program 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3365 31 4428 (StagedOperand.l1Program 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4466 CarryRowPrograms.middle :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3396 40 4466 CarryRowPrograms.middle
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4512 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3436 2 4512 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4515 (l2Program 1 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3439 30 4515 (l2Program 1 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4551 (l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3469 30 4551 (l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4587 (l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3499 30 4587 (l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4623 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3529 29 4623 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4657 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3558 1 4657 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4658 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3559 29 4658 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4692 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3588 29 4692 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4726 (l2Program 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3617 30 4726 (l2Program 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4761 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3647 21 4761 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4790 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3668 16 4790 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join8 : Block Artifact.submissionArtifact .Osaka 4200 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3179 1 4200 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL1Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4200 = true :=
  Artifact.isValidJumpDest_index 3179 (by rfl)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4514 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3438 1 4514 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4514 = true :=
  Artifact.isValidJumpDest_index 3438 (by rfl)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4169 = true :=
  Artifact.isValidJumpDest_index 3148 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4352 = true :=
  Artifact.isValidJumpDest_index 3303 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4657 = true :=
  Artifact.isValidJumpDest_index 3558 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks

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

end Challenge.Modexp.Submission.Proofs.Fast.CarryRowBlocks
