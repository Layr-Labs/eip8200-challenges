import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths

open KnownInputCompactPaths

def prePath : List Located :=
  [opAt 2880 (.Dup ⟨2, by decide⟩),
   pushAt 2881 1 6,
   opAt 2882 .SHR,
   pushAt 2883 1 21,
   opAt 2884 .MUL,
   pushAt 2885 2 4953,
   opAt 2886 .ADD,
   pushAt 2887 1 20,
   opAt 2888 (.Swap ⟨0, by decide⟩),
   pushAt 2889 0 0]

def postPath : List Located :=
  [pushAt 2891 0 0,
   opAt 2892 .MLOAD,
   pushAt 2893 1 224,
   opAt 2894 .SHR,
   pushAt 2895 1 32,
   opAt 2896 .MSTORE,
   pushAt 2897 1 4,
   opAt 2898 .MLOAD,
   pushAt 2899 1 224,
   opAt 2900 .SHR,
   pushAt 2901 1 64,
   opAt 2902 .MSTORE,
   pushAt 2903 1 8,
   opAt 2904 .MLOAD,
   pushAt 2905 1 224,
   opAt 2906 .SHR,
   pushAt 2907 1 96,
   opAt 2908 .MSTORE,
   pushAt 2909 1 12,
   opAt 2910 .MLOAD,
   pushAt 2911 1 224,
   opAt 2912 .SHR,
   pushAt 2913 1 128,
   opAt 2914 .MSTORE,
   pushAt 2915 1 16,
   opAt 2916 .MLOAD,
   pushAt 2917 1 224,
   opAt 2918 .SHR,
   pushAt 2919 1 160,
   opAt 2920 .MSTORE,
   opAt 2921 .POP,
   opAt 2922 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths
