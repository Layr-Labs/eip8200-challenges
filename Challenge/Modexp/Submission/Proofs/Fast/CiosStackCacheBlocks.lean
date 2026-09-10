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

def entry : Block Artifact.submissionArtifact .Osaka 4160 (CiosStackCachePrograms.entry) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3129 64 4160 (CiosStackCachePrograms.entry)
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4243 (CiosStackCachePrograms.out) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3193 5 4243 (CiosStackCachePrograms.out)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4248 (dispatchFor 4405) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3198 3 4248 (dispatchFor 4405)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4253 (l1StepFor 7) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3201 34 4253 (l1StepFor 7)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4291 (l1StepFor 6) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3235 34 4291 (l1StepFor 6)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4329 (l1StepFor 5) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3269 34 4329 (l1StepFor 5)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4367 (l1StepFor 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3303 34 4367 (l1StepFor 4)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4405 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3337 1 4405 ([.op .JUMPDEST])
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4406 (l1StepFor 3) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3338 34 4406 (l1StepFor 3)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4444 (l1StepFor 2) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3372 33 4444 (l1StepFor 2)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4477 (l1StepFor 1) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3405 33 4477 (l1StepFor 1)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4510 (l1Last) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3438 32 4510 (l1Last)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4542 (midProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3470 28 4542 (midProgram)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4576 (dispatchFor 4729) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3498 3 4576 (dispatchFor 4729)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4581 (l2BodyFor 6) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3501 32 4581 (l2BodyFor 6)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4618 (l2BodyFor 5) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3533 32 4618 (l2BodyFor 5)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 4655 (l2BodyFor 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3565 32 4655 (l2BodyFor 4)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 4692 (l2BodyFor 3) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3597 32 4692 (l2BodyFor 3)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 4729 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3629 1 4729 ([.op .JUMPDEST])
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 4730 (l2BodyFor 2) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3630 31 4730 (l2BodyFor 2)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 4764 (l2BodyFor 1) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3661 30 4764 (l2BodyFor 1)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 4794 (l2BodyFor 0) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3691 30 4794 (l2BodyFor 0)
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block Artifact.submissionArtifact .Osaka 4824 (tailProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3721 23 4824 (tailProgram)
    (by decide) (by rfl) (by rfl) (by decide)

def exit : Block Artifact.submissionArtifact .Osaka 4855 (CiosStackCachePrograms.exit) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3744 19 4855 (CiosStackCachePrograms.exit)
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
  jumpOut := by exact Artifact.isValidJumpDest_index 3193 (by rfl)
  jumpL1 := by exact Artifact.isValidJumpDest_index 3337 (by rfl)
  jumpL2 := by exact Artifact.isValidJumpDest_index 3629 (by rfl)
  jumpCsub := by exact Artifact.isValidJumpDest_index 1617 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2^256; rw [Challenge.Modexp.submissionBytecode_size]; decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheBlocks
