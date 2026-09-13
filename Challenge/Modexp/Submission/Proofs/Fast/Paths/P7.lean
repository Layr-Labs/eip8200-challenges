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
  [opAt 806 .JUMPDEST,
   pushAt 807 1 1,
   opAt 808 (.Swap ⟨0, by decide⟩),
   opAt 809 .SUB,
   opAt 810 (.Dup ⟨0, by decide⟩),
   pushAt 811 2 1178,
   opAt 812 .JUMPI]

/-- Instructions 1376..1508, pc 1984..2065. -/
def blk1376 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 813 .POP,
   opAt 814 .POP,
   opAt 815 .JUMP]

/-- Instructions 1509..1487, pc 2066..2100. -/
def blk1379 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 816 .JUMPDEST,
   pushAt 817 2 2688,
   opAt 818 .MLOAD,
   opAt 819 (.Dup ⟨0, by decide⟩),
   pushAt 820 1 64,
   opAt 821 .ADD,
   opAt 822 .CALLDATASIZE,
   pushAt 823 2 2048,
   opAt 824 .CALLDATACOPY,
   opAt 825 (.Dup ⟨0, by decide⟩),
   opAt 826 (.Dup ⟨3, by decide⟩),
   opAt 827 .ADD,
   pushAt 828 1 32,
   opAt 829 (.Swap ⟨0, by decide⟩),
   opAt 830 .SUB,
   pushAt 831 1 32,
   opAt 832 (.Dup ⟨4, by decide⟩),
   opAt 833 .SUB,
   opAt 834 (.Swap ⟨3, by decide⟩),
   opAt 835 .POP,
   opAt 836 (.Swap ⟨0, by decide⟩),
   opAt 837 .POP,
   pushAt 838 1 32,
   opAt 839 (.Dup ⟨2, by decide⟩),
   opAt 840 .SUB,
   opAt 841 (.Swap ⟨1, by decide⟩),
   opAt 842 .POP]

/-- Instructions 1536..1550, pc 2101..2121. -/
def blk1406 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 843 .JUMPDEST,
   opAt 844 (.Dup ⟨0, by decide⟩),
   opAt 845 .MLOAD,
   pushAt 846 0 0,
   pushAt 847 2 2784,
   opAt 848 .MLOAD,
   opAt 849 (.Dup ⟨4, by decide⟩),
   pushAt 850 2 2688,
   opAt 851 .MLOAD,
   opAt 852 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast
