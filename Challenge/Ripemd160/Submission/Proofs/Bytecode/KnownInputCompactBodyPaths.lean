import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths

open KnownInputCompactPaths

def prePath : List Located :=
  [opAt 2870 (.Dup ⟨2, by decide⟩),
   pushAt 2871 1 6,
   opAt 2872 .SHR,
   pushAt 2873 1 21,
   opAt 2874 .MUL,
   pushAt 2875 2 4958,
   opAt 2876 .ADD,
   pushAt 2877 2 320,
   opAt 2878 (.Swap ⟨0, by decide⟩),
   pushAt 2879 1 208]

def postPath : List Located :=
  [pushAt 2881 0 0,
   opAt 2882 .MLOAD,
   pushAt 2883 1 224,
   opAt 2884 .SHR,
   pushAt 2885 1 32,
   opAt 2886 .MSTORE,
   pushAt 2887 1 4,
   opAt 2888 .MLOAD,
   pushAt 2889 1 224,
   opAt 2890 .SHR,
   pushAt 2891 1 64,
   opAt 2892 .MSTORE,
   pushAt 2893 1 8,
   opAt 2894 .MLOAD,
   pushAt 2895 1 24,
   opAt 2896 .SHR,
   pushAt 2897 1 96,
   opAt 2898 .MSTORE,
   pushAt 2899 1 12,
   opAt 2900 .MLOAD,
   pushAt 2901 1 224,
   opAt 2902 .SHR,
   pushAt 2903 1 128,
   opAt 2904 .MSTORE,
   pushAt 2905 1 16,
   opAt 2906 .MLOAD,
   pushAt 2907 1 224,
   opAt 2908 .SHR,
   pushAt 2909 1 160,
   opAt 2910 .MSTORE,
   opAt 2911 .POP,
   opAt 2912 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths
