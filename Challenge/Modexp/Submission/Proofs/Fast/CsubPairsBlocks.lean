import Challenge.Modexp.Submission.Proofs.Fast.CsubPairsTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CsubPairsBlocks

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open CsubPairsCore CsubPairsGuard CsubPairsEntry CsubPairsTail

def entry : Block Artifact.submissionArtifact .Osaka 2225 entryProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 1647 11 2225 entryProgram
    (by decide) (by rfl) (by rfl) (by decide)

def first : Block Artifact.submissionArtifact .Osaka 2241 limbProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 1658 29 2241 limbProgram
    (by decide) (by rfl) (by rfl) (by decide)

def second : Block Artifact.submissionArtifact .Osaka 2366 limbProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 1687 29 2366 limbProgram
    (by decide) (by rfl) (by rfl) (by decide)

def guard : Block Artifact.submissionArtifact .Osaka 2491 guardProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 1716 5 2491 guardProgram
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block Artifact.submissionArtifact .Osaka 2500 tailProgram :=
  WindowTwentyOneSlice.block Artifact.allWellFormed 1721 14 2500 tailProgram
    (by decide) (by rfl) (by rfl) (by decide)

def blocks : CsubPairsTrace.Blocks Artifact.submissionArtifact :=
  ⟨entry, first, second, guard, tail⟩

theorem jumpFirst : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2241 = true :=
  Artifact.isValidJumpDest_index 1658 (by rfl)

theorem jumpSecond : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2366 = true :=
  Artifact.isValidJumpDest_index 1687 (by rfl)

def environment (s : State)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Environment Artifact.submissionArtifact .Osaka s :=
  ⟨by change Challenge.Modexp.submissionBytecode.size < 2 ^ 256
      rw [Challenge.Modexp.submissionBytecode_size]
      decide,
    hcode, hfork, hrun, hnp⟩

end Challenge.Modexp.Submission.Proofs.Fast.CsubPairsBlocks
