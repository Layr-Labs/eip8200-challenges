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
  WindowTwentyOneSlice.block Artifact.allWellFormed 3085 64 4076 StagedOperand.fullEntryProgram
    (by decide) (by decide) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4173 outProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3152 3 4173 outProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4202 l1DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3181 2 4202 l1DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4176 CiosReadonly.commonFirstProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3155 26 4176 CiosReadonly.commonFirstProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4204 (StagedOperand.l1Program 192 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3183 32 4204 (StagedOperand.l1Program 192 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4242 (StagedOperand.l1Program 160 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3215 32 4242 (StagedOperand.l1Program 160 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4280 (StagedOperand.l1Program 128 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3247 32 4280 (StagedOperand.l1Program 128 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4356 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3311 1 4356 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4318 (StagedOperand.l1Program 96 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3279 32 4318 (StagedOperand.l1Program 96 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4356 (StagedOperand.l1Program 64 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3311 32 4356 (StagedOperand.l1Program 64 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4394 (StagedOperand.l1Program 32 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3343 32 4394 (StagedOperand.l1Program 32 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4432 (StagedOperand.l1Program 0 2112) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3375 32 4432 (StagedOperand.l1Program 0 2112)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4470 CarryRowPrograms.middle :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3407 40 4470 CarryRowPrograms.middle
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4516 l2DispatchProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3447 2 4516 l2DispatchProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4519 (l2Program 1 192 2304 2336) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3450 31 4519 (l2Program 1 192 2304 2336)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4555 (l2Program 1 160 2272 2304) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3481 31 4555 (l2Program 1 160 2272 2304)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4591 (l2Program 1 128 2240 2272) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3512 31 4591 (l2Program 1 128 2240 2272)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4627 (CiosReadonlyExtra.extraProgram 0 2208 2240) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3543 30 4627 (CiosReadonlyExtra.extraProgram 0 2208 2240)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4661 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3573 1 4661 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4662 (CiosReadonlyExtra.extraProgram 1 2176 2208) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3574 30 4662 (CiosReadonlyExtra.extraProgram 1 2176 2208)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4696 (CiosReadonlyExtra.extraProgram 2 2144 2176) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3604 30 4696 (CiosReadonlyExtra.extraProgram 2 2144 2176)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4730 (l2Program 0 0 2112 2144) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3634 31 4730 (l2Program 0 0 2112 2144)
    (by decide) (by rfl) (by rfl) (by decide)

def tailLoop : Block Artifact.submissionArtifact .Osaka 4765 CarryRowPrograms.tail :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3665 21 4765 CarryRowPrograms.tail
    (by decide) (by rfl) (by rfl) (by decide)

def exitBlock : Block Artifact.submissionArtifact .Osaka 4794 CiosReadonly.fullExitProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3686 16 4794 CiosReadonly.fullExitProgram
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join8 : Block Artifact.submissionArtifact .Osaka 4204 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3183 1 4204 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL1Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4204 = true :=
  Artifact.isValidJumpDest_index 3183 (by rfl)

def l2Join8 : Block Artifact.submissionArtifact .Osaka 4518 joinProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3449 1 4518 joinProgram
    (by decide) (by rfl) (by rfl) (by decide)

theorem jumpDestL2Eight : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4518 = true :=
  Artifact.isValidJumpDest_index 3449 (by rfl)

theorem jumpDest4595 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4173 = true :=
  Artifact.isValidJumpDest_index 3152 (by rfl)

theorem jumpDest4757 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4356 = true :=
  Artifact.isValidJumpDest_index 3311 (by rfl)

theorem jumpDest5112 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4661 = true :=
  Artifact.isValidJumpDest_index 3573 (by rfl)

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
