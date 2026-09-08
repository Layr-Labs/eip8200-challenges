import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBinding
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL1
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNL2
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNDispatch
import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNLoopTests

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNLoopPaths

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof WindowNineBinding MonproKNDispatchWords

/-- Exact raw252f locations, to be supplied by a separately verified Artifact. -/
structure L1Paths (artifact : ProgramArtifact) (fork : Fork) where
  dispatch : Block artifact fork 4070 MonproKNDispatch.l1Program
  body : ∀ slot, slot < 8 → Block artifact fork (l1PC slot) MonproKNL1.program
  test : Block artifact fork 4393 MonproKNLoopTests.l1TestProgram
  exit : Block artifact fork 4400 MonproKNLoopTests.l1ExitProgram
  jump : ∀ slot, slot < 8 → Decode.isValidJumpDest artifact.code (l1PC slot) = true
  middle : Decode.isValidJumpDest artifact.code 2008 = true

/-- L2 has n-1 MACs and falls through to the unchanged row-tail calculation. -/
structure L2Paths (artifact : ProgramArtifact) (fork : Fork) where
  dispatch : Block artifact fork 2077 MonproKNDispatch.l2Program
  body : ∀ slot, slot < 8 → Block artifact fork (l2PC slot) MonproKNL2.program
  test : Block artifact fork 2426 MonproKNLoopTests.l2TestProgram
  jump : ∀ slot, slot < 8 → Decode.isValidJumpDest artifact.code (l2PC slot) = true

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNLoopPaths
