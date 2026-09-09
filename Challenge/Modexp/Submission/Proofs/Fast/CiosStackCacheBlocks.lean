import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheBlockInterface
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open CiosStackCache

def entry : Block Artifact.submissionArtifact .Osaka 4447 (CiosStackCachePrograms.entry) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3189 62 4447 (CiosStackCachePrograms.entry)
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4591 (CiosStackCachePrograms.out) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3251 5 4591 (CiosStackCachePrograms.out)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4596 (dispatchFor 4753) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3256 3 4596 (dispatchFor 4753)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4601 (l1StepFor 7) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3259 34 4601 (l1StepFor 7)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4639 (l1StepFor 6) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3293 34 4639 (l1StepFor 6)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4677 (l1StepFor 5) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3327 34 4677 (l1StepFor 5)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4715 (l1StepFor 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3361 34 4715 (l1StepFor 4)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4753 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3395 1 4753 ([.op .JUMPDEST])
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4754 (l1StepFor 3) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3396 34 4754 (l1StepFor 3)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4792 (l1StepFor 2) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3430 33 4792 (l1StepFor 2)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4825 (l1StepFor 1) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3463 33 4825 (l1StepFor 1)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4858 (l1Last) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3496 32 4858 (l1Last)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4890 (midProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3528 28 4890 (midProgram)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4924 (dispatchFor 5081) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3556 3 4924 (dispatchFor 5081)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4929 (l2BodyFor 6) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3559 32 4929 (l2BodyFor 6)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4967 (l2BodyFor 5) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3591 32 4967 (l2BodyFor 5)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 5005 (l2BodyFor 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3623 32 5005 (l2BodyFor 4)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5043 (l2BodyFor 3) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3655 32 5043 (l2BodyFor 3)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5081 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3687 1 5081 ([.op .JUMPDEST])
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5082 (l2BodyFor 2) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3688 31 5082 (l2BodyFor 2)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5117 (l2BodyFor 1) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3719 30 5117 (l2BodyFor 1)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5147 (l2BodyFor 0) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3749 30 5147 (l2BodyFor 0)
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block Artifact.submissionArtifact .Osaka 5177 (tailProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3779 23 5177 (tailProgram)
    (by decide) (by rfl) (by rfl) (by decide)

def exit : Block Artifact.submissionArtifact .Osaka 5208 (CiosStackCachePrograms.exit) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3802 19 5208 (CiosStackCachePrograms.exit)
    (by decide) (by rfl) (by rfl) (by decide)

def kernelBlocks : KernelBlocks Artifact.submissionArtifact where
  entry := entry
  out := out
  l1Dispatch := l1Dispatch
  l1Mac0 := l1Mac0
  l1Mac1 := l1Mac1
  l1Mac2 := l1Mac2
  l1Mac3 := l1Mac3
  l1Join := l1Join
  l1Mac4 := l1Mac4
  l1Mac5 := l1Mac5
  l1Mac6 := l1Mac6
  l1Mac7 := l1Mac7
  mid := mid
  l2Dispatch := l2Dispatch
  l2Mac0 := l2Mac0
  l2Mac1 := l2Mac1
  l2Mac2 := l2Mac2
  l2Mac3 := l2Mac3
  l2Join := l2Join
  l2Mac4 := l2Mac4
  l2Mac5 := l2Mac5
  l2Mac6 := l2Mac6
  tail := tail
  exit := exit
  jumpOut := by exact Artifact.isValidJumpDest_index 3251 (by rfl)
  jumpL1 := by exact Artifact.isValidJumpDest_index 3395 (by rfl)
  jumpL2 := by exact Artifact.isValidJumpDest_index 3687 (by rfl)
  jumpCsub := by exact Artifact.isValidJumpDest_index 1662 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheBlocks
