import Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateArtifact
import Challenge.Modexp.Submission.Proofs.Fast.TnMod128Chain
import Challenge.Modexp.Submission.Proofs.Fast.TnCacheReductionTrace
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneSlice

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast TnM128CandidateArtifact

def l2Eight : Block submissionArtifact .Osaka 3630 (TnMod128Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 2836 198 3630 (TnMod128Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 3758 (TnMod128Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 2948 86 3758 (TnMod128Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def cachedCell : Block submissionArtifact .Osaka 3694 (TnMod128Trace.program) :=
  WindowTwentyOneSlice.block allWellFormed 2892 28 3694 (TnMod128Trace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def middle8 : Block submissionArtifact .Osaka 3607 (TnCacheRowTrace.middle8) :=
  WindowTwentyOneSlice.block allWellFormed 2817 19 3607 (TnCacheRowTrace.middle8)
    (by decide) (by rfl) (by rfl) (by decide)

def middleCopy : Block submissionArtifact .Osaka 5493 (TnCacheRowTrace.middle4 ++ [.push 2 3758, .op .JUMP]) :=
  WindowTwentyOneSlice.block allWellFormed 4388 19 5493 (TnCacheRowTrace.middle4 ++ [.push 2 3758, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block submissionArtifact .Osaka 3856 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block allWellFormed 3034 15 3856 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 3883 (TnCacheFrameOps.flush13) :=
  WindowTwentyOneSlice.block allWellFormed 3054 3 3883 (TnCacheFrameOps.flush13)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3257 (TnCacheFrameOps.reset13) :=
  WindowTwentyOneSlice.block allWellFormed 2534 3 3257 (TnCacheFrameOps.reset13)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
