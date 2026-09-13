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
  [opAt 814 .JUMPDEST,
   pushAt 815 1 1,
   opAt 816 (.Swap ⟨0, by decide⟩),
   opAt 817 .SUB,
   opAt 818 (.Dup ⟨0, by decide⟩),
   pushAt 819 2 1195,
   opAt 820 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 821 .POP,
   opAt 822 .POP,
   opAt 823 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 824 .JUMPDEST,
   pushAt 825 2 2688,
   opAt 826 .MLOAD,
   opAt 827 (.Dup ⟨0, by decide⟩),
   pushAt 828 1 64,
   opAt 829 .ADD,
   opAt 830 .CALLDATASIZE,
   pushAt 831 2 2048,
   opAt 832 .CALLDATACOPY,
   opAt 833 (.Dup ⟨0, by decide⟩),
   opAt 834 (.Dup ⟨3, by decide⟩),
   opAt 835 .ADD,
   pushAt 836 1 32,
   opAt 837 (.Swap ⟨0, by decide⟩),
   opAt 838 .SUB,
   pushAt 839 1 32,
   opAt 840 (.Dup ⟨4, by decide⟩),
   opAt 841 .SUB,
   opAt 842 (.Swap ⟨3, by decide⟩),
   opAt 843 .POP,
   opAt 844 (.Swap ⟨0, by decide⟩),
   opAt 845 .POP,
   pushAt 846 1 32,
   opAt 847 (.Dup ⟨2, by decide⟩),
   opAt 848 .SUB,
   opAt 849 (.Swap ⟨1, by decide⟩),
   opAt 850 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 851 .JUMPDEST,
   opAt 852 (.Dup ⟨0, by decide⟩),
   opAt 853 .MLOAD,
   pushAt 854 0 0,
   pushAt 855 2 2784,
   opAt 856 .MLOAD,
   opAt 857 (.Dup ⟨4, by decide⟩),
   pushAt 858 2 2688,
   opAt 859 .MLOAD,
   opAt 860 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
