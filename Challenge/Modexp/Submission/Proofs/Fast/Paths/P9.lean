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
  [opAt 912 .POP,
   opAt 913 .POP,
   opAt 914 (.Dup ⟨0, by decide⟩),
   pushAt 915 2 2080,
   opAt 916 .MLOAD,
   opAt 917 .ADD,
   opAt 918 (.Dup ⟨0, by decide⟩),
   pushAt 919 2 2080,
   opAt 920 .MSTORE,
   opAt 921 .LT,
   pushAt 922 2 2048,
   opAt 923 .MSTORE,
   pushAt 924 2 2784,
   opAt 925 .MLOAD,
   opAt 926 .MLOAD,
   pushAt 927 2 2720,
   opAt 928 .MLOAD,
   opAt 929 .MUL,
   opAt 930 (.Dup ⟨0, by decide⟩),
   pushAt 931 2 2752,
   opAt 932 .MLOAD,
   opAt 933 .MLOAD,
   opAt 934 (.Dup ⟨1, by decide⟩),
   opAt 935 (.Dup ⟨1, by decide⟩),
   opAt 936 .MUL,
   opAt 937 (.Swap ⟨1, by decide⟩),
   pushAt 938 0 0,
   opAt 939 .NOT,
   opAt 940 (.Swap ⟨1, by decide⟩),
   opAt 941 .MULMOD,
   opAt 942 (.Dup ⟨1, by decide⟩),
   opAt 943 (.Dup ⟨1, by decide⟩),
   opAt 944 .LT,
   opAt 945 (.Dup ⟨2, by decide⟩),
   opAt 946 .ADD,
   opAt 947 (.Swap ⟨0, by decide⟩),
   opAt 948 .SUB,
   opAt 949 (.Swap ⟨0, by decide⟩),
   pushAt 950 0 0,
   opAt 951 .LT,
   opAt 952 .ADD,
   pushAt 953 2 2784,
   opAt 954 .MLOAD,
   pushAt 955 1 32,
   opAt 956 (.Swap ⟨0, by decide⟩),
   opAt 957 .SUB,
   pushAt 958 2 2752,
   opAt 959 .MLOAD,
   pushAt 960 1 32,
   opAt 961 (.Swap ⟨0, by decide⟩),
   opAt 962 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
