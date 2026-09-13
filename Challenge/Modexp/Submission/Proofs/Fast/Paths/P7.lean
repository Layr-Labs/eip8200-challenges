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
  [opAt 807 .JUMPDEST,
   pushAt 808 1 1,
   opAt 809 (.Swap ⟨0, by decide⟩),
   opAt 810 .SUB,
   opAt 811 (.Dup ⟨0, by decide⟩),
   pushAt 812 2 1179,
   opAt 813 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 814 .POP,
   opAt 815 .POP,
   opAt 816 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 817 .JUMPDEST,
   pushAt 818 2 2688,
   opAt 819 .MLOAD,
   opAt 820 (.Dup ⟨0, by decide⟩),
   pushAt 821 1 64,
   opAt 822 .ADD,
   opAt 823 .CALLDATASIZE,
   pushAt 824 2 2048,
   opAt 825 .CALLDATACOPY,
   opAt 826 (.Dup ⟨0, by decide⟩),
   opAt 827 (.Dup ⟨3, by decide⟩),
   opAt 828 .ADD,
   pushAt 829 1 32,
   opAt 830 (.Swap ⟨0, by decide⟩),
   opAt 831 .SUB,
   pushAt 832 1 32,
   opAt 833 (.Dup ⟨4, by decide⟩),
   opAt 834 .SUB,
   opAt 835 (.Swap ⟨3, by decide⟩),
   opAt 836 .POP,
   opAt 837 (.Swap ⟨0, by decide⟩),
   opAt 838 .POP,
   pushAt 839 1 32,
   opAt 840 (.Dup ⟨2, by decide⟩),
   opAt 841 .SUB,
   opAt 842 (.Swap ⟨1, by decide⟩),
   opAt 843 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 844 .JUMPDEST,
   opAt 845 (.Dup ⟨0, by decide⟩),
   opAt 846 .MLOAD,
   pushAt 847 0 0,
   pushAt 848 2 2784,
   opAt 849 .MLOAD,
   opAt 850 (.Dup ⟨4, by decide⟩),
   pushAt 851 2 2688,
   opAt 852 .MLOAD,
   opAt 853 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
