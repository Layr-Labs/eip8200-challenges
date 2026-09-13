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
  [opAt 905 .POP,
   opAt 906 .POP,
   opAt 907 (.Dup ⟨0, by decide⟩),
   pushAt 908 2 2080,
   opAt 909 .MLOAD,
   opAt 910 .ADD,
   opAt 911 (.Dup ⟨0, by decide⟩),
   pushAt 912 2 2080,
   opAt 913 .MSTORE,
   opAt 914 .LT,
   pushAt 915 2 2048,
   opAt 916 .MSTORE,
   pushAt 917 2 2784,
   opAt 918 .MLOAD,
   opAt 919 .MLOAD,
   pushAt 920 2 2720,
   opAt 921 .MLOAD,
   opAt 922 .MUL,
   opAt 923 (.Dup ⟨0, by decide⟩),
   pushAt 924 2 2752,
   opAt 925 .MLOAD,
   opAt 926 .MLOAD,
   opAt 927 (.Dup ⟨1, by decide⟩),
   opAt 928 (.Dup ⟨1, by decide⟩),
   opAt 929 .MUL,
   opAt 930 (.Swap ⟨1, by decide⟩),
   pushAt 931 0 0,
   opAt 932 .NOT,
   opAt 933 (.Swap ⟨1, by decide⟩),
   opAt 934 .MULMOD,
   opAt 935 (.Dup ⟨1, by decide⟩),
   opAt 936 (.Dup ⟨1, by decide⟩),
   opAt 937 .LT,
   opAt 938 (.Dup ⟨2, by decide⟩),
   opAt 939 .ADD,
   opAt 940 (.Swap ⟨0, by decide⟩),
   opAt 941 .SUB,
   opAt 942 (.Swap ⟨0, by decide⟩),
   pushAt 943 0 0,
   opAt 944 .LT,
   opAt 945 .ADD,
   pushAt 946 2 2784,
   opAt 947 .MLOAD,
   pushAt 948 1 32,
   opAt 949 (.Swap ⟨0, by decide⟩),
   opAt 950 .SUB,
   pushAt 951 2 2752,
   opAt 952 .MLOAD,
   pushAt 953 1 32,
   opAt 954 (.Swap ⟨0, by decide⟩),
   opAt 955 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
