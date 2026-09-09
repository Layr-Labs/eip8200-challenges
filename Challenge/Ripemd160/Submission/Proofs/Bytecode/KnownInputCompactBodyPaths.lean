import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths

open KnownInputCompactPaths

def prePath : List Located :=
  [opAt 2890 (.Dup ⟨2, by decide⟩),
   pushAt 2891 1 6,
   opAt 2892 .SHR,
   pushAt 2893 1 21,
   opAt 2894 .MUL,
   pushAt 2895 2 4958,
   opAt 2896 .ADD,
   pushAt 2897 1 20,
   opAt 2898 (.Swap ⟨0, by decide⟩),
   pushAt 2899 0 0]

def postPath : List Located :=
  [pushAt 2901 0 0,
   opAt 2902 .MLOAD,
   pushAt 2903 1 224,
   opAt 2904 .SHR,
   pushAt 2905 1 32,
   opAt 2906 .MSTORE,
   pushAt 2907 1 4,
   opAt 2908 .MLOAD,
   pushAt 2909 1 224,
   opAt 2910 .SHR,
   pushAt 2911 1 64,
   opAt 2912 .MSTORE,
   pushAt 2913 1 8,
   opAt 2914 .MLOAD,
   pushAt 2915 1 224,
   opAt 2916 .SHR,
   pushAt 2917 1 96,
   opAt 2918 .MSTORE,
   pushAt 2919 1 12,
   opAt 2920 .MLOAD,
   pushAt 2921 1 224,
   opAt 2922 .SHR,
   pushAt 2923 1 128,
   opAt 2924 .MSTORE,
   pushAt 2925 1 16,
   opAt 2926 .MLOAD,
   pushAt 2927 1 224,
   opAt 2928 .SHR,
   pushAt 2929 1 160,
   opAt 2930 .MSTORE,
   opAt 2931 .POP,
   opAt 2932 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths
