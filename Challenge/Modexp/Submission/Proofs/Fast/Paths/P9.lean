import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1599..1600). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1599..1600, pc 2177..2245. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 827 .POP,
   opAt 828 .POP,
   opAt 829 (.Dup ⟨0, by decide⟩),
   pushAt 830 2 2080,
   opAt 831 .MLOAD,
   opAt 832 .ADD,
   opAt 833 (.Dup ⟨0, by decide⟩),
   pushAt 834 2 2080,
   opAt 835 .MSTORE,
   opAt 836 .LT,
   pushAt 837 2 2048,
   opAt 838 .MSTORE,
   pushAt 839 2 2784,
   opAt 840 .MLOAD,
   opAt 841 .MLOAD,
   pushAt 842 2 2720,
   opAt 843 .MLOAD,
   opAt 844 .MUL,
   opAt 845 (.Dup ⟨0, by decide⟩),
   pushAt 846 2 2752,
   opAt 847 .MLOAD,
   opAt 848 .MLOAD,
   opAt 849 (.Dup ⟨1, by decide⟩),
   opAt 850 (.Dup ⟨1, by decide⟩),
   opAt 851 .MUL,
   opAt 852 (.Swap ⟨1, by decide⟩),
   pushAt 853 0 0,
   opAt 854 .NOT,
   opAt 855 (.Swap ⟨1, by decide⟩),
   opAt 856 .MULMOD,
   opAt 857 (.Dup ⟨1, by decide⟩),
   opAt 858 (.Dup ⟨1, by decide⟩),
   opAt 859 .LT,
   opAt 860 (.Dup ⟨2, by decide⟩),
   opAt 861 .ADD,
   opAt 862 (.Swap ⟨0, by decide⟩),
   opAt 863 .SUB,
   opAt 864 (.Swap ⟨0, by decide⟩),
   pushAt 865 0 0,
   opAt 866 .LT,
   opAt 867 .ADD,
   pushAt 868 2 2784,
   opAt 869 .MLOAD,
   pushAt 870 1 32,
   opAt 871 (.Swap ⟨0, by decide⟩),
   opAt 872 .SUB,
   pushAt 873 2 2752,
   opAt 874 .MLOAD,
   pushAt 875 1 32,
   opAt 876 (.Swap ⟨0, by decide⟩),
   opAt 877 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
