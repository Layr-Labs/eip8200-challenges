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
  entry : Block art .Osaka 4476 CiosStackCachePrograms.entry
  out : Block art .Osaka 4620 CiosStackCachePrograms.out
  l1Dispatch : Block art .Osaka 4625 (dispatchFor 4782)
  l1Mac0 : Block art .Osaka 4630 (l1StepFor 7)
  l1Mac1 : Block art .Osaka 4668 (l1StepFor 6)
  l1Mac2 : Block art .Osaka 4706 (l1StepFor 5)
  l1Mac3 : Block art .Osaka 4744 (l1StepFor 4)
  l1Join : Block art .Osaka 4782 [.op .JUMPDEST]
  l1Mac4 : Block art .Osaka 4783 (l1StepFor 3)
  l1Mac5 : Block art .Osaka 4821 (l1StepFor 2)
  l1Mac6 : Block art .Osaka 4854 (l1StepFor 1)
  l1Mac7 : Block art .Osaka 4887 l1Last
  mid : Block art .Osaka 4919 midProgram
  l2Dispatch : Block art .Osaka 4953 (dispatchFor 5110)
  l2Mac0 : Block art .Osaka 4958 (l2BodyFor 6)
  l2Mac1 : Block art .Osaka 4996 (l2BodyFor 5)
  l2Mac2 : Block art .Osaka 5034 (l2BodyFor 4)
  l2Mac3 : Block art .Osaka 5072 (l2BodyFor 3)
  l2Join : Block art .Osaka 5110 [.op .JUMPDEST]
  l2Mac4 : Block art .Osaka 5111 (l2BodyFor 2)
  l2Mac5 : Block art .Osaka 5146 (l2BodyFor 1)
  l2Mac6 : Block art .Osaka 5176 (l2BodyFor 0)
  tail : Block art .Osaka 5206 tailProgram
  exit : Block art .Osaka 5237 CiosStackCachePrograms.exit
  jumpOut : Decode.isValidJumpDest art.code 4620 = true
  jumpL1 : Decode.isValidJumpDest art.code 4782 = true
  jumpL2 : Decode.isValidJumpDest art.code 5110 = true
  jumpCsub : Decode.isValidJumpDest art.code 2288 = true

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache
