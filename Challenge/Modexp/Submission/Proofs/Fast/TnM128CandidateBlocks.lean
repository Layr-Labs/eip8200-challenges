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

def l2Eight : Block submissionArtifact .Osaka 3871 (TnMod128Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 3035 201 3871 (TnMod128Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 4003 (TnMod128Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 3150 86 4003 (TnMod128Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def cachedCell : Block submissionArtifact .Osaka 3939 (TnMod128Trace.program) :=
  WindowTwentyOneSlice.block allWellFormed 3094 28 3939 (TnMod128Trace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def middle8 : Block submissionArtifact .Osaka 3850 (TnCacheRowTrace.middle8) :=
  WindowTwentyOneSlice.block allWellFormed 3015 20 3850 (TnCacheRowTrace.middle8)
    (by decide) (by rfl) (by rfl) (by decide)

def middleCopy : Block submissionArtifact .Osaka 5475 (TnCacheRowTrace.middle4 ++ [.push 2 4003, .op .JUMP]) :=
  WindowTwentyOneSlice.block allWellFormed 4349 21 5475 (TnCacheRowTrace.middle4 ++ [.push 2 4003, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block submissionArtifact .Osaka 4101 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block allWellFormed 3236 17 4101 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 4152 (TnCacheFrameOps.flush13) :=
  WindowTwentyOneSlice.block allWellFormed 3253 3 4152 (TnCacheFrameOps.flush13)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3500 (TnCacheFrameOps.reset13) :=
  WindowTwentyOneSlice.block allWellFormed 2727 3 3500 (TnCacheFrameOps.reset13)
    (by decide) (by rfl) (by rfl) (by decide)

def againReset : Block submissionArtifact .Osaka 4223 (TnCacheFrameOps.reset13) :=
  WindowTwentyOneSlice.block allWellFormed 3303 3 4223 (TnCacheFrameOps.reset13)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
