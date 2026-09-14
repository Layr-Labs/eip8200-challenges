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
  [opAt 808 .JUMPDEST,
   pushAt 809 1 1,
   opAt 810 (.Swap ⟨0, by decide⟩),
   opAt 811 .SUB,
   opAt 812 (.Dup ⟨0, by decide⟩),
   pushAt 813 2 1179,
   opAt 814 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 815 .POP,
   opAt 816 .POP,
   opAt 817 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 818 .JUMPDEST,
   pushAt 819 2 2688,
   opAt 820 .MLOAD,
   opAt 821 (.Dup ⟨0, by decide⟩),
   pushAt 822 1 64,
   opAt 823 .ADD,
   opAt 824 .CALLDATASIZE,
   pushAt 825 2 2048,
   opAt 826 .CALLDATACOPY,
   opAt 827 (.Dup ⟨0, by decide⟩),
   opAt 828 (.Dup ⟨3, by decide⟩),
   opAt 829 .ADD,
   pushAt 830 1 32,
   opAt 831 (.Swap ⟨0, by decide⟩),
   opAt 832 .SUB,
   pushAt 833 1 32,
   opAt 834 (.Dup ⟨4, by decide⟩),
   opAt 835 .SUB,
   opAt 836 (.Swap ⟨3, by decide⟩),
   opAt 837 .POP,
   opAt 838 (.Swap ⟨0, by decide⟩),
   opAt 839 .POP,
   pushAt 840 1 32,
   opAt 841 (.Dup ⟨2, by decide⟩),
   opAt 842 .SUB,
   opAt 843 (.Swap ⟨1, by decide⟩),
   opAt 844 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 845 .JUMPDEST,
   opAt 846 (.Dup ⟨0, by decide⟩),
   opAt 847 .MLOAD,
   pushAt 848 0 0,
   pushAt 849 2 2784,
   opAt 850 .MLOAD,
   opAt 851 (.Dup ⟨4, by decide⟩),
   pushAt 852 2 2688,
   opAt 853 .MLOAD,
   opAt 854 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
