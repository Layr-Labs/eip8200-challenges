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

def entry : Block Artifact.submissionArtifact .Osaka 4476 (CiosStackCachePrograms.entry) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3188 62 4476 (CiosStackCachePrograms.entry)
    (by decide) (by rfl) (by rfl) (by decide)

def out : Block Artifact.submissionArtifact .Osaka 4620 (CiosStackCachePrograms.out) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3250 5 4620 (CiosStackCachePrograms.out)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Dispatch : Block Artifact.submissionArtifact .Osaka 4625 (dispatchFor 4782) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3255 3 4625 (dispatchFor 4782)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac0 : Block Artifact.submissionArtifact .Osaka 4630 (l1StepFor 7) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3258 34 4630 (l1StepFor 7)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac1 : Block Artifact.submissionArtifact .Osaka 4668 (l1StepFor 6) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3292 34 4668 (l1StepFor 6)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac2 : Block Artifact.submissionArtifact .Osaka 4706 (l1StepFor 5) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3326 34 4706 (l1StepFor 5)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac3 : Block Artifact.submissionArtifact .Osaka 4744 (l1StepFor 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3360 34 4744 (l1StepFor 4)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Join : Block Artifact.submissionArtifact .Osaka 4782 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3394 1 4782 ([.op .JUMPDEST])
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac4 : Block Artifact.submissionArtifact .Osaka 4783 (l1StepFor 3) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3395 34 4783 (l1StepFor 3)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac5 : Block Artifact.submissionArtifact .Osaka 4821 (l1StepFor 2) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3429 33 4821 (l1StepFor 2)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac6 : Block Artifact.submissionArtifact .Osaka 4854 (l1StepFor 1) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3462 33 4854 (l1StepFor 1)
    (by decide) (by rfl) (by rfl) (by decide)

def l1Mac7 : Block Artifact.submissionArtifact .Osaka 4887 (l1Last) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3495 32 4887 (l1Last)
    (by decide) (by rfl) (by rfl) (by decide)

def mid : Block Artifact.submissionArtifact .Osaka 4919 (midProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3527 28 4919 (midProgram)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Dispatch : Block Artifact.submissionArtifact .Osaka 4953 (dispatchFor 5110) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3555 3 4953 (dispatchFor 5110)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac0 : Block Artifact.submissionArtifact .Osaka 4958 (l2BodyFor 6) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3558 32 4958 (l2BodyFor 6)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac1 : Block Artifact.submissionArtifact .Osaka 4996 (l2BodyFor 5) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3590 32 4996 (l2BodyFor 5)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac2 : Block Artifact.submissionArtifact .Osaka 5034 (l2BodyFor 4) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3622 32 5034 (l2BodyFor 4)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac3 : Block Artifact.submissionArtifact .Osaka 5072 (l2BodyFor 3) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3654 32 5072 (l2BodyFor 3)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Join : Block Artifact.submissionArtifact .Osaka 5110 ([.op .JUMPDEST]) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3686 1 5110 ([.op .JUMPDEST])
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac4 : Block Artifact.submissionArtifact .Osaka 5111 (l2BodyFor 2) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3687 31 5111 (l2BodyFor 2)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac5 : Block Artifact.submissionArtifact .Osaka 5146 (l2BodyFor 1) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3718 30 5146 (l2BodyFor 1)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Mac6 : Block Artifact.submissionArtifact .Osaka 5176 (l2BodyFor 0) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3748 30 5176 (l2BodyFor 0)
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block Artifact.submissionArtifact .Osaka 5206 (tailProgram) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3778 23 5206 (tailProgram)
    (by decide) (by rfl) (by rfl) (by decide)

def exit : Block Artifact.submissionArtifact .Osaka 5237 (CiosStackCachePrograms.exit) :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 3801 19 5237 (CiosStackCachePrograms.exit)
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
  jumpOut := by exact Artifact.isValidJumpDest_index 3250 (by rfl)
  jumpL1 := by exact Artifact.isValidJumpDest_index 3394 (by rfl)
  jumpL2 := by exact Artifact.isValidJumpDest_index 3686 (by rfl)
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
