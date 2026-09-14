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
  [opAt 825 .POP,
   opAt 826 .POP,
   opAt 827 (.Dup ⟨0, by decide⟩),
   pushAt 828 2 2080,
   opAt 829 .MLOAD,
   opAt 830 .ADD,
   opAt 831 (.Dup ⟨0, by decide⟩),
   pushAt 832 2 2080,
   opAt 833 .MSTORE,
   opAt 834 .LT,
   pushAt 835 2 2048,
   opAt 836 .MSTORE,
   pushAt 837 2 2784,
   opAt 838 .MLOAD,
   opAt 839 .MLOAD,
   pushAt 840 2 2720,
   opAt 841 .MLOAD,
   opAt 842 .MUL,
   opAt 843 (.Dup ⟨0, by decide⟩),
   pushAt 844 2 2752,
   opAt 845 .MLOAD,
   opAt 846 .MLOAD,
   opAt 847 (.Dup ⟨1, by decide⟩),
   opAt 848 (.Dup ⟨1, by decide⟩),
   opAt 849 .MUL,
   opAt 850 (.Swap ⟨1, by decide⟩),
   pushAt 851 0 0,
   opAt 852 .NOT,
   opAt 853 (.Swap ⟨1, by decide⟩),
   opAt 854 .MULMOD,
   opAt 855 (.Dup ⟨1, by decide⟩),
   opAt 856 (.Dup ⟨1, by decide⟩),
   opAt 857 .LT,
   opAt 858 (.Dup ⟨2, by decide⟩),
   opAt 859 .ADD,
   opAt 860 (.Swap ⟨0, by decide⟩),
   opAt 861 .SUB,
   opAt 862 (.Swap ⟨0, by decide⟩),
   pushAt 863 0 0,
   opAt 864 .LT,
   opAt 865 .ADD,
   pushAt 866 2 2784,
   opAt 867 .MLOAD,
   pushAt 868 1 32,
   opAt 869 (.Swap ⟨0, by decide⟩),
   opAt 870 .SUB,
   pushAt 871 2 2752,
   opAt 872 .MLOAD,
   pushAt 873 1 32,
   opAt 874 (.Swap ⟨0, by decide⟩),
   opAt 875 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
