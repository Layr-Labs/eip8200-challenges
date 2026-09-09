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
  entry : Block art .Osaka 4451 CiosStackCachePrograms.entry
  out : Block art .Osaka 4595 CiosStackCachePrograms.out
  l1Dispatch : Block art .Osaka 4600 (dispatchFor 4757)
  l1Mac0 : Block art .Osaka 4605 (l1StepFor 7)
  l1Mac1 : Block art .Osaka 4643 (l1StepFor 6)
  l1Mac2 : Block art .Osaka 4681 (l1StepFor 5)
  l1Mac3 : Block art .Osaka 4719 (l1StepFor 4)
  l1Join : Block art .Osaka 4757 [.op .JUMPDEST]
  l1Mac4 : Block art .Osaka 4758 (l1StepFor 3)
  l1Mac5 : Block art .Osaka 4796 (l1StepFor 2)
  l1Mac6 : Block art .Osaka 4829 (l1StepFor 1)
  l1Mac7 : Block art .Osaka 4862 l1Last
  mid : Block art .Osaka 4894 midProgram
  l2Dispatch : Block art .Osaka 4928 (dispatchFor 5085)
  l2Mac0 : Block art .Osaka 4933 (l2BodyFor 6)
  l2Mac1 : Block art .Osaka 4971 (l2BodyFor 5)
  l2Mac2 : Block art .Osaka 5009 (l2BodyFor 4)
  l2Mac3 : Block art .Osaka 5047 (l2BodyFor 3)
  l2Join : Block art .Osaka 5085 [.op .JUMPDEST]
  l2Mac4 : Block art .Osaka 5086 (l2BodyFor 2)
  l2Mac5 : Block art .Osaka 5121 (l2BodyFor 1)
  l2Mac6 : Block art .Osaka 5151 (l2BodyFor 0)
  tail : Block art .Osaka 5181 tailProgram
  exit : Block art .Osaka 5212 CiosStackCachePrograms.exit
  jumpOut : Decode.isValidJumpDest art.code 4595 = true
  jumpL1 : Decode.isValidJumpDest art.code 4757 = true
  jumpL2 : Decode.isValidJumpDest art.code 5085 = true
  jumpCsub : Decode.isValidJumpDest art.code 2288 = true

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache
