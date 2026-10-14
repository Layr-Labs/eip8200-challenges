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

def l2Eight : Block submissionArtifact .Osaka 3862 (TnMod128Chain.fullProgram 8) :=
  WindowTwentyOneSlice.block allWellFormed 3023 199 3862 (TnMod128Chain.fullProgram 8)
    (by decide) (by rfl) (by rfl) (by decide)

def l2Four : Block submissionArtifact .Osaka 3991 (TnMod128Chain.fullProgram 4) :=
  WindowTwentyOneSlice.block allWellFormed 3136 86 3991 (TnMod128Chain.fullProgram 4)
    (by decide) (by rfl) (by rfl) (by decide)

def cachedCell : Block submissionArtifact .Osaka 3927 (TnMod128Trace.program) :=
  WindowTwentyOneSlice.block allWellFormed 3080 28 3927 (TnMod128Trace.program)
    (by decide) (by rfl) (by rfl) (by decide)

def middle8 : Block submissionArtifact .Osaka 3839 (TnCacheRowTrace.middle8) :=
  WindowTwentyOneSlice.block allWellFormed 3004 19 3839 (TnCacheRowTrace.middle8)
    (by decide) (by rfl) (by rfl) (by decide)

def middleCopy : Block submissionArtifact .Osaka 5495 (TnCacheRowTrace.middle4 ++ [.push 2 3991, .op .JUMP]) :=
  WindowTwentyOneSlice.block allWellFormed 4372 21 5495 (TnCacheRowTrace.middle4 ++ [.push 2 3991, .op .JUMP])
    (by decide) (by rfl) (by rfl) (by decide)

def tail : Block submissionArtifact .Osaka 4089 (TnCacheRowTrace.tail) :=
  WindowTwentyOneSlice.block allWellFormed 3222 15 4089 (TnCacheRowTrace.tail)
    (by decide) (by rfl) (by rfl) (by decide)

def flush : Block submissionArtifact .Osaka 4116 (TnCacheFrameOps.flush13) :=
  WindowTwentyOneSlice.block allWellFormed 3242 3 4116 (TnCacheFrameOps.flush13)
    (by decide) (by rfl) (by rfl) (by decide)

def afterSquareReset : Block submissionArtifact .Osaka 3488 (TnCacheFrameOps.reset13) :=
  WindowTwentyOneSlice.block allWellFormed 2719 3 3488 (TnCacheFrameOps.reset13)
    (by decide) (by rfl) (by rfl) (by decide)

end Challenge.Modexp.Submission.Proofs.Fast.TnM128CandidateBlocks
