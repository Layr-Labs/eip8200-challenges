import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 9 (instructions 1598..1600). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1598..1600, pc 2176..2244. -/
def blk1469 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 904 .POP,
   opAt 905 .POP,
   opAt 906 (.Dup ⟨0, by decide⟩),
   pushAt 907 2 2080,
   opAt 908 .MLOAD,
   opAt 909 .ADD,
   opAt 910 (.Dup ⟨0, by decide⟩),
   pushAt 911 2 2080,
   opAt 912 .MSTORE,
   opAt 913 .LT,
   pushAt 914 2 2048,
   opAt 915 .MSTORE,
   pushAt 916 2 2784,
   opAt 917 .MLOAD,
   opAt 918 .MLOAD,
   pushAt 919 2 2720,
   opAt 920 .MLOAD,
   opAt 921 .MUL,
   opAt 922 (.Dup ⟨0, by decide⟩),
   pushAt 923 2 2752,
   opAt 924 .MLOAD,
   opAt 925 .MLOAD,
   opAt 926 (.Dup ⟨1, by decide⟩),
   opAt 927 (.Dup ⟨1, by decide⟩),
   opAt 928 .MUL,
   opAt 929 (.Swap ⟨1, by decide⟩),
   pushAt 930 0 0,
   opAt 931 .NOT,
   opAt 932 (.Swap ⟨1, by decide⟩),
   opAt 933 .MULMOD,
   opAt 934 (.Dup ⟨1, by decide⟩),
   opAt 935 (.Dup ⟨1, by decide⟩),
   opAt 936 .LT,
   opAt 937 (.Dup ⟨2, by decide⟩),
   opAt 938 .ADD,
   opAt 939 (.Swap ⟨0, by decide⟩),
   opAt 940 .SUB,
   opAt 941 (.Swap ⟨0, by decide⟩),
   pushAt 942 0 0,
   opAt 943 .LT,
   opAt 944 .ADD,
   pushAt 945 2 2784,
   opAt 946 .MLOAD,
   pushAt 947 1 32,
   opAt 948 (.Swap ⟨0, by decide⟩),
   opAt 949 .SUB,
   pushAt 950 2 2752,
   opAt 951 .MLOAD,
   pushAt 952 1 32,
   opAt 953 (.Swap ⟨0, by decide⟩),
   opAt 954 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast
