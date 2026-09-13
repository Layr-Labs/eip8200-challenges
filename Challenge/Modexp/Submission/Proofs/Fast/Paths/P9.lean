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
  [opAt 907 .POP,
   opAt 908 .POP,
   opAt 909 (.Dup ⟨0, by decide⟩),
   pushAt 910 2 2080,
   opAt 911 .MLOAD,
   opAt 912 .ADD,
   opAt 913 (.Dup ⟨0, by decide⟩),
   pushAt 914 2 2080,
   opAt 915 .MSTORE,
   opAt 916 .LT,
   pushAt 917 2 2048,
   opAt 918 .MSTORE,
   pushAt 919 2 2784,
   opAt 920 .MLOAD,
   opAt 921 .MLOAD,
   pushAt 922 2 2720,
   opAt 923 .MLOAD,
   opAt 924 .MUL,
   opAt 925 (.Dup ⟨0, by decide⟩),
   pushAt 926 2 2752,
   opAt 927 .MLOAD,
   opAt 928 .MLOAD,
   opAt 929 (.Dup ⟨1, by decide⟩),
   opAt 930 (.Dup ⟨1, by decide⟩),
   opAt 931 .MUL,
   opAt 932 (.Swap ⟨1, by decide⟩),
   pushAt 933 0 0,
   opAt 934 .NOT,
   opAt 935 (.Swap ⟨1, by decide⟩),
   opAt 936 .MULMOD,
   opAt 937 (.Dup ⟨1, by decide⟩),
   opAt 938 (.Dup ⟨1, by decide⟩),
   opAt 939 .LT,
   opAt 940 (.Dup ⟨2, by decide⟩),
   opAt 941 .ADD,
   opAt 942 (.Swap ⟨0, by decide⟩),
   opAt 943 .SUB,
   opAt 944 (.Swap ⟨0, by decide⟩),
   pushAt 945 0 0,
   opAt 946 .LT,
   opAt 947 .ADD,
   pushAt 948 2 2784,
   opAt 949 .MLOAD,
   pushAt 950 1 32,
   opAt 951 (.Swap ⟨0, by decide⟩),
   opAt 952 .SUB,
   pushAt 953 2 2752,
   opAt 954 .MLOAD,
   pushAt 955 1 32,
   opAt 956 (.Swap ⟨0, by decide⟩),
   opAt 957 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
