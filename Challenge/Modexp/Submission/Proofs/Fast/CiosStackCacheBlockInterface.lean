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
  entry : Block art .Osaka 4160 CiosStackCachePrograms.entry
  out : Block art .Osaka 4243 CiosStackCachePrograms.out
  l1Dispatch : Block art .Osaka 4248 (dispatchFor 4405)
  l1Mac0 : Block art .Osaka 4253 (l1StepFor 7)
  l1Mac1 : Block art .Osaka 4291 (l1StepFor 6)
  l1Mac2 : Block art .Osaka 4329 (l1StepFor 5)
  l1Mac3 : Block art .Osaka 4367 (l1StepFor 4)
  l1Join : Block art .Osaka 4405 [.op .JUMPDEST]
  l1Mac4 : Block art .Osaka 4406 (l1StepFor 3)
  l1Mac5 : Block art .Osaka 4444 (l1StepFor 2)
  l1Mac6 : Block art .Osaka 4477 (l1StepFor 1)
  l1Mac7 : Block art .Osaka 4510 l1Last
  mid : Block art .Osaka 4542 midProgram
  l2Dispatch : Block art .Osaka 4576 (dispatchFor 4729)
  l2Mac0 : Block art .Osaka 4581 (l2BodyFor 6)
  l2Mac1 : Block art .Osaka 4618 (l2BodyFor 5)
  l2Mac2 : Block art .Osaka 4655 (l2BodyFor 4)
  l2Mac3 : Block art .Osaka 4692 (l2BodyFor 3)
  l2Join : Block art .Osaka 4729 [.op .JUMPDEST]
  l2Mac4 : Block art .Osaka 4730 (l2BodyFor 2)
  l2Mac5 : Block art .Osaka 4764 (l2BodyFor 1)
  l2Mac6 : Block art .Osaka 4794 (l2BodyFor 0)
  tail : Block art .Osaka 4824 tailProgram
  exit : Block art .Osaka 4855 CiosStackCachePrograms.exit
  jumpOut : Decode.isValidJumpDest art.code 4243 = true
  jumpL1 : Decode.isValidJumpDest art.code 4405 = true
  jumpL2 : Decode.isValidJumpDest art.code 4729 = true
  jumpCsub : Decode.isValidJumpDest art.code 2220 = true

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache
