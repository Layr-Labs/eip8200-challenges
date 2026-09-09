import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheL1Steps
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheL2Steps
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheControl
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMidStep
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheTailStep
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding

/-- Every executable block required by the complete cached CIOS path. This
interface allows the row proof to remain independent of artifact generation. -/
structure KernelBlocks (art : ProgramArtifact) where
  entry : Block art .Osaka 4447 CiosStackCachePrograms.entry
  out : Block art .Osaka 4591 CiosStackCachePrograms.out
  l1Dispatch : Block art .Osaka 4596 (dispatchFor 4753)
  l1Mac0 : Block art .Osaka 4601 (l1StepFor 7)
  l1Mac1 : Block art .Osaka 4639 (l1StepFor 6)
  l1Mac2 : Block art .Osaka 4677 (l1StepFor 5)
  l1Mac3 : Block art .Osaka 4715 (l1StepFor 4)
  l1Join : Block art .Osaka 4753 [.op .JUMPDEST]
  l1Mac4 : Block art .Osaka 4754 (l1StepFor 3)
  l1Mac5 : Block art .Osaka 4792 (l1StepFor 2)
  l1Mac6 : Block art .Osaka 4825 (l1StepFor 1)
  l1Mac7 : Block art .Osaka 4858 l1Last
  mid : Block art .Osaka 4890 midProgram
  l2Dispatch : Block art .Osaka 4924 (dispatchFor 5081)
  l2Mac0 : Block art .Osaka 4929 (l2BodyFor 6)
  l2Mac1 : Block art .Osaka 4967 (l2BodyFor 5)
  l2Mac2 : Block art .Osaka 5005 (l2BodyFor 4)
  l2Mac3 : Block art .Osaka 5043 (l2BodyFor 3)
  l2Join : Block art .Osaka 5081 [.op .JUMPDEST]
  l2Mac4 : Block art .Osaka 5082 (l2BodyFor 2)
  l2Mac5 : Block art .Osaka 5117 (l2BodyFor 1)
  l2Mac6 : Block art .Osaka 5147 (l2BodyFor 0)
  tail : Block art .Osaka 5177 tailProgram
  exit : Block art .Osaka 5208 CiosStackCachePrograms.exit
  jumpOut : Decode.isValidJumpDest art.code 4591 = true
  jumpL1 : Decode.isValidJumpDest art.code 4753 = true
  jumpL2 : Decode.isValidJumpDest art.code 5081 = true
  jumpCsub : Decode.isValidJumpDest art.code 2288 = true

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache
