import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths

open KnownInputCompactPaths

def prePath : List Located :=
  [opAt 2883 (.Dup ⟨2, by decide⟩),
   pushAt 2884 1 6,
   opAt 2885 .SHR,
   pushAt 2886 1 21,
   opAt 2887 .MUL,
   pushAt 2888 2 4958,
   opAt 2889 .ADD,
   pushAt 2890 1 20,
   opAt 2891 (.Swap ⟨0, by decide⟩),
   pushAt 2892 0 0]

def postPath : List Located :=
  [pushAt 2894 0 0,
   opAt 2895 .MLOAD,
   pushAt 2896 1 224,
   opAt 2897 .SHR,
   pushAt 2898 1 32,
   opAt 2899 .MSTORE,
   pushAt 2900 1 4,
   opAt 2901 .MLOAD,
   pushAt 2902 1 224,
   opAt 2903 .SHR,
   pushAt 2904 1 64,
   opAt 2905 .MSTORE,
   pushAt 2906 1 8,
   opAt 2907 .MLOAD,
   pushAt 2908 1 224,
   opAt 2909 .SHR,
   pushAt 2910 1 96,
   opAt 2911 .MSTORE,
   pushAt 2912 1 12,
   opAt 2913 .MLOAD,
   pushAt 2914 1 224,
   opAt 2915 .SHR,
   pushAt 2916 1 128,
   opAt 2917 .MSTORE,
   pushAt 2918 1 16,
   opAt 2919 .MLOAD,
   pushAt 2920 1 224,
   opAt 2921 .SHR,
   pushAt 2922 1 160,
   opAt 2923 .MSTORE,
   opAt 2924 .POP,
   opAt 2925 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths
