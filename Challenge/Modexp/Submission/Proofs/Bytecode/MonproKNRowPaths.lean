import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBinding
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPrograms

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPaths

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding MonproKNRowPrograms

/-- Exact raw252f row blocks. Concrete Artifact factories are a separate layer. -/
structure RowPaths (artifact : ProgramArtifact) (fork : Fork) where
  entry : Block artifact fork 1939 entryProgram
  out : Block artifact fork 1982 outProgram
  stub : Block artifact fork 2003 stubProgram
  middle : Block artifact fork 2008 midProgram
  tail : Block artifact fork 2435 tailProgram
  exit : Block artifact fork 2471 exitProgram
  outerJump : Decode.isValidJumpDest artifact.code 1982 = true
  l1Jump : Decode.isValidJumpDest artifact.code 4070 = true
  csubJump : Decode.isValidJumpDest artifact.code 2655 = true

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNRowPaths
