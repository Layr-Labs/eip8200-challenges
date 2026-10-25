import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnMod128Chain
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheReductionTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CycleSubmission.Global.Fast.TnM128CandidateBlocks
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast

def l2Four : Block CycleSubmission.Artifact.artifact .Osaka 3298 (TnMod128Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2559 86 3298 (TnMod128Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)


def middleCopy : Block CycleSubmission.Artifact.artifact .Osaka 3916 (TnCacheRowTrace.middle4 ++ [.push 2 3298, .op .JUMP]) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 3030 19 3916 (TnCacheRowTrace.middle4 ++ [.push 2 3298, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)


def tail : Block CycleSubmission.Artifact.artifact .Osaka 3396 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2645 15 3396 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)


def flush : Block CycleSubmission.Artifact.artifact .Osaka 3423 (TnCacheFrameOps.flush13) :=
  WindowTwentyOneSlice.block CycleSubmission.Artifact.wellFormed 2665 3 3423 (TnCacheFrameOps.flush13)
    (by decide) (by rfl) (by rfl) (by decide)


 /- The old after-square reset13 block has been superseded by the fused
constant-pointer entry. The production proof is TnM128FusedEntry.prefixBlock,
which requires the structural zero carried by SquareLoop. -/

end CycleSubmission.Global.Fast.TnM128CandidateBlocks
