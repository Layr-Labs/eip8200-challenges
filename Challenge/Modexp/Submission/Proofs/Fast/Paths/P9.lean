import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1599..1600). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1599..1600, pc 2176..2244. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 906 .POP,
   opAt 907 .POP,
   opAt 908 (.Dup ⟨0, by decide⟩),
   pushAt 909 2 2080,
   opAt 910 .MLOAD,
   opAt 911 .ADD,
   opAt 912 (.Dup ⟨0, by decide⟩),
   pushAt 913 2 2080,
   opAt 914 .MSTORE,
   opAt 915 .LT,
   pushAt 916 2 2048,
   opAt 917 .MSTORE,
   pushAt 918 2 2784,
   opAt 919 .MLOAD,
   opAt 920 .MLOAD,
   pushAt 921 2 2720,
   opAt 922 .MLOAD,
   opAt 923 .MUL,
   opAt 924 (.Dup ⟨0, by decide⟩),
   pushAt 925 2 2752,
   opAt 926 .MLOAD,
   opAt 927 .MLOAD,
   opAt 928 (.Dup ⟨1, by decide⟩),
   opAt 929 (.Dup ⟨1, by decide⟩),
   opAt 930 .MUL,
   opAt 931 (.Swap ⟨1, by decide⟩),
   pushAt 932 0 0,
   opAt 933 .NOT,
   opAt 934 (.Swap ⟨1, by decide⟩),
   opAt 935 .MULMOD,
   opAt 936 (.Dup ⟨1, by decide⟩),
   opAt 937 (.Dup ⟨1, by decide⟩),
   opAt 938 .LT,
   opAt 939 (.Dup ⟨2, by decide⟩),
   opAt 940 .ADD,
   opAt 941 (.Swap ⟨0, by decide⟩),
   opAt 942 .SUB,
   opAt 943 (.Swap ⟨0, by decide⟩),
   pushAt 944 0 0,
   opAt 945 .LT,
   opAt 946 .ADD,
   pushAt 947 2 2784,
   opAt 948 .MLOAD,
   pushAt 949 1 32,
   opAt 950 (.Swap ⟨0, by decide⟩),
   opAt 951 .SUB,
   pushAt 952 2 2752,
   opAt 953 .MLOAD,
   pushAt 954 1 32,
   opAt 955 (.Swap ⟨0, by decide⟩),
   opAt 956 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
