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

def entry : Block Artifact.submissionArtifact .Osaka 4481 (CiosStackCachePrograms.entry) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3210 64 4481 (CiosStackCachePrograms.entry)
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4595 (CiosStackCachePrograms.out) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3274 5 4595 (CiosStackCachePrograms.out)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4600 (dispatchFor 4757) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3279 3 4600 (dispatchFor 4757)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4605 (l1StepFor 7) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3282 34 4605 (l1StepFor 7)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4643 (l1StepFor 6) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3316 34 4643 (l1StepFor 6)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4681 (l1StepFor 5) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3350 34 4681 (l1StepFor 5)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4719 (l1StepFor 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3384 34 4719 (l1StepFor 4)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4757 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3418 1 4757 ([.op .JUMPDEST])
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4758 (l1StepFor 3) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3419 34 4758 (l1StepFor 3)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4796 (l1StepFor 2) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3453 33 4796 (l1StepFor 2)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4829 (l1StepFor 1) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3486 33 4829 (l1StepFor 1)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4862 (l1Last) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3519 32 4862 (l1Last)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4894 (midProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3551 28 4894 (midProgram)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4928 (dispatchFor 5085) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3579 3 4928 (dispatchFor 5085)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4933 (l2BodyFor 6) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3582 32 4933 (l2BodyFor 6)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4971 (l2BodyFor 5) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3614 32 4971 (l2BodyFor 5)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 5009 (l2BodyFor 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3646 32 5009 (l2BodyFor 4)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5047 (l2BodyFor 3) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3678 32 5047 (l2BodyFor 3)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5085 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3710 1 5085 ([.op .JUMPDEST])
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5086 (l2BodyFor 2) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3711 31 5086 (l2BodyFor 2)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5121 (l2BodyFor 1) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3742 30 5121 (l2BodyFor 1)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5151 (l2BodyFor 0) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3772 30 5151 (l2BodyFor 0)
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block Artifact.submissionArtifact .Osaka 5181 (tailProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3802 23 5181 (tailProgram)
    (by decide) (by rfl) (by rfl) (by decide)

def exit : Block Artifact.submissionArtifact .Osaka 5212 (CiosStackCachePrograms.exit) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3825 19 5212 (CiosStackCachePrograms.exit)
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
  jumpOut := by exact Artifact.isValidJumpDest_index 3274 (by rfl)
  jumpL1 := by exact Artifact.isValidJumpDest_index 3418 (by rfl)
  jumpL2 := by exact Artifact.isValidJumpDest_index 3710 (by rfl)
  jumpCsub := by exact Artifact.isValidJumpDest_index 1668 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheBlocks
