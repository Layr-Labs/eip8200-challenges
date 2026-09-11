import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactPaths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths

open KnownInputCompactPaths

def prePath : List Located :=
  [opAt 2862 (.Dup ⟨2, by decide⟩),
   pushAt 2863 1 6,
   opAt 2864 .SHR,
   pushAt 2865 1 21,
   opAt 2866 .MUL,
   pushAt 2867 2 4964,
   opAt 2868 .ADD,
   pushAt 2869 2 320,
   opAt 2870 (.Swap ⟨0, by decide⟩),
   pushAt 2871 1 208]

def postPath : List Located :=
  [pushAt 2873 0 0,
   opAt 2874 .MLOAD,
   pushAt 2875 1 224,
   opAt 2876 .SHR,
   pushAt 2877 1 32,
   opAt 2878 .MSTORE,
   pushAt 2879 1 4,
   opAt 2880 .MLOAD,
   pushAt 2881 1 224,
   opAt 2882 .SHR,
   pushAt 2883 1 64,
   opAt 2884 .MSTORE,
   pushAt 2885 1 8,
   opAt 2886 .MLOAD,
   pushAt 2887 1 24,
   opAt 2888 .SHR,
   pushAt 2889 1 96,
   opAt 2890 .MSTORE,
   pushAt 2891 1 12,
   opAt 2892 .MLOAD,
   pushAt 2893 1 224,
   opAt 2894 .SHR,
   pushAt 2895 1 128,
   opAt 2896 .MSTORE,
   pushAt 2897 1 16,
   opAt 2898 .MLOAD,
   pushAt 2899 1 224,
   opAt 2900 .SHR,
   pushAt 2901 1 160,
   opAt 2902 .MSTORE,
   opAt 2903 .POP,
   opAt 2904 .JUMP]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactBodyPaths
