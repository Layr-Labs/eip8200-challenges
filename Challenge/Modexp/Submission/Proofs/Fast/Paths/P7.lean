import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 7 (instructions 1451..1550). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1451..1505, pc 2053..2062. -/
def blk1369 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 809 .JUMPDEST,
   pushAt 810 0 0,
   opAt 811 .NOT,
   opAt 812 .ADD,
   opAt 813 (.Dup ⟨0, by decide⟩),
   pushAt 814 3 1195,
   opAt 815 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 816 .POP,
   opAt 817 .POP,
   opAt 818 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 819 .JUMPDEST,
   pushAt 820 2 2688,
   opAt 821 .MLOAD,
   opAt 822 (.Dup ⟨0, by decide⟩),
   pushAt 823 1 64,
   opAt 824 .ADD,
   opAt 825 .CALLDATASIZE,
   pushAt 826 2 2048,
   opAt 827 .CALLDATACOPY,
   opAt 828 (.Dup ⟨0, by decide⟩),
   opAt 829 (.Dup ⟨3, by decide⟩),
   opAt 830 .ADD,
   pushAt 831 1 32,
   opAt 832 (.Swap ⟨0, by decide⟩),
   opAt 833 .SUB,
   pushAt 834 1 32,
   opAt 835 (.Dup ⟨4, by decide⟩),
   opAt 836 .SUB,
   opAt 837 (.Swap ⟨3, by decide⟩),
   opAt 838 .POP,
   opAt 839 (.Swap ⟨0, by decide⟩),
   opAt 840 .POP,
   pushAt 841 1 32,
   opAt 842 (.Dup ⟨2, by decide⟩),
   opAt 843 .SUB,
   opAt 844 (.Swap ⟨1, by decide⟩),
   opAt 845 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 846 .JUMPDEST,
   opAt 847 (.Dup ⟨0, by decide⟩),
   opAt 848 .MLOAD,
   pushAt 849 0 0,
   pushAt 850 2 2784,
   opAt 851 .MLOAD,
   opAt 852 (.Dup ⟨4, by decide⟩),
   pushAt 853 2 2688,
   opAt 854 .MLOAD,
   opAt 855 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
