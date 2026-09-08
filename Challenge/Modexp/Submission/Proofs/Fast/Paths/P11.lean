import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 11 (retained ADDMOD entry). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1848..1874, pc 2480..2512. -/
def blk1600 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1848 .JUMPDEST,
   pushAt 1849 2 9344,
   opAt 1850 .MLOAD,
   opAt 1851 (.Dup ⟨0, by decide⟩),
   opAt 1852 (.Dup ⟨2, by decide⟩),
   opAt 1853 .ADD,
   pushAt 1854 1 32,
   opAt 1855 (.Swap ⟨0, by decide⟩),
   opAt 1856 .SUB,
   opAt 1857 (.Dup ⟨1, by decide⟩),
   opAt 1858 (.Dup ⟨4, by decide⟩),
   opAt 1859 .ADD,
   pushAt 1860 1 32,
   opAt 1861 (.Swap ⟨0, by decide⟩),
   opAt 1862 .SUB,
   opAt 1863 (.Swap ⟨2, by decide⟩),
   opAt 1864 .POP,
   opAt 1865 (.Swap ⟨2, by decide⟩),
   opAt 1866 .POP,
   opAt 1867 .POP,
   pushAt 1868 2 9440,
   opAt 1869 .MLOAD,
   pushAt 1870 0 0,
   opAt 1871 .JUMPDEST,
   opAt 1872 .JUMPDEST,
   opAt 1873 (.Swap ⟨2, by decide⟩),
   opAt 1874 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast
