import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 10 (instructions 1519..1568 plus the appended L2 copies). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
/-! The original L2 entry is now a fixed-width jump stub.  The appended
    pair of copies removes the loop branch from the common path. -/
def blk1519 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1519 .JUMPDEST,
   pushAt 1520 2 4643,
   opAt 1521 .JUMP]

/-! The appended two-way L2 body. -/
def blkUL2_0 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   opAt 2874 .JUMPDEST,
   opAt 2875 (.Dup ⟨3, by decide⟩),
   opAt 2876 (.Dup ⟨1, by decide⟩),
   opAt 2877 .MLOAD,
   opAt 2878 (.Dup ⟨1, by decide⟩),
   opAt 2879 (.Dup ⟨1, by decide⟩),
   opAt 2880 .MUL,
   opAt 2881 (.Swap ⟨1, by decide⟩),
   pushAt 2882 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2883 (.Swap ⟨1, by decide⟩),
   opAt 2884 .MULMOD,
   opAt 2885 (.Dup ⟨1, by decide⟩),
   opAt 2886 (.Dup ⟨1, by decide⟩),
   opAt 2887 .LT,
   opAt 2888 (.Dup ⟨2, by decide⟩),
   opAt 2889 .ADD,
   opAt 2890 (.Swap ⟨0, by decide⟩),
   opAt 2891 .SUB,
   opAt 2892 (.Dup ⟨3, by decide⟩),
   opAt 2893 .MLOAD,
   opAt 2894 (.Swap ⟨1, by decide⟩),
   opAt 2895 (.Dup ⟨2, by decide⟩),
   opAt 2896 .ADD,
   opAt 2897 (.Swap ⟨1, by decide⟩),
   opAt 2898 (.Dup ⟨2, by decide⟩),
   opAt 2899 .LT,
   opAt 2900 .ADD,
   opAt 2901 (.Swap ⟨0, by decide⟩),
   opAt 2902 (.Dup ⟨4, by decide⟩),
   opAt 2903 .ADD,
   opAt 2904 (.Swap ⟨3, by decide⟩),
   opAt 2905 (.Dup ⟨4, by decide⟩),
   opAt 2906 .LT,
   opAt 2907 .ADD,
   opAt 2908 (.Swap ⟨2, by decide⟩),
   opAt 2909 (.Dup ⟨2, by decide⟩),
   pushAt 2910 1 32,
   opAt 2911 .ADD,
   opAt 2912 .MSTORE,
   pushAt 2913 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2914 .ADD,
   opAt 2915 (.Swap ⟨0, by decide⟩),
   pushAt 2916 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2917 .ADD,
   opAt 2918 (.Swap ⟨0, by decide⟩)
]

def blkUL2_1 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   opAt 2919 .JUMPDEST,
   opAt 2920 (.Dup ⟨3, by decide⟩),
   opAt 2921 (.Dup ⟨1, by decide⟩),
   opAt 2922 .MLOAD,
   opAt 2923 (.Dup ⟨1, by decide⟩),
   opAt 2924 (.Dup ⟨1, by decide⟩),
   opAt 2925 .MUL,
   opAt 2926 (.Swap ⟨1, by decide⟩),
   pushAt 2927 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2928 (.Swap ⟨1, by decide⟩),
   opAt 2929 .MULMOD,
   opAt 2930 (.Dup ⟨1, by decide⟩),
   opAt 2931 (.Dup ⟨1, by decide⟩),
   opAt 2932 .LT,
   opAt 2933 (.Dup ⟨2, by decide⟩),
   opAt 2934 .ADD,
   opAt 2935 (.Swap ⟨0, by decide⟩),
   opAt 2936 .SUB,
   opAt 2937 (.Dup ⟨3, by decide⟩),
   opAt 2938 .MLOAD,
   opAt 2939 (.Swap ⟨1, by decide⟩),
   opAt 2940 (.Dup ⟨2, by decide⟩),
   opAt 2941 .ADD,
   opAt 2942 (.Swap ⟨1, by decide⟩),
   opAt 2943 (.Dup ⟨2, by decide⟩),
   opAt 2944 .LT,
   opAt 2945 .ADD,
   opAt 2946 (.Swap ⟨0, by decide⟩),
   opAt 2947 (.Dup ⟨4, by decide⟩),
   opAt 2948 .ADD,
   opAt 2949 (.Swap ⟨3, by decide⟩),
   opAt 2950 (.Dup ⟨4, by decide⟩),
   opAt 2951 .LT,
   opAt 2952 .ADD,
   opAt 2953 (.Swap ⟨2, by decide⟩),
   opAt 2954 (.Dup ⟨2, by decide⟩),
   pushAt 2955 1 32,
   opAt 2956 .ADD,
   opAt 2957 .MSTORE,
   pushAt 2958 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2959 .ADD,
   opAt 2960 (.Swap ⟨0, by decide⟩),
   pushAt 2961 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2962 .ADD,
   opAt 2963 (.Swap ⟨0, by decide⟩)
]

def blkTestL2 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2964 2 8224,
   opAt 2965 (.Dup ⟨1, by decide⟩),
   opAt 2966 .GT,
   pushAt 2967 2 4661,
   opAt 2968 .JUMPI]

def blkTestL2X :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2964 2 8224,
   opAt 2965 (.Dup ⟨1, by decide⟩),
   opAt 2966 .GT,
   pushAt 2967 2 4661,
   opAt 2968 .JUMPI,
   pushAt 2969 2 2391,
   opAt 2970 .JUMP]

def blkDispL2 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2862 .JUMPDEST,
   opAt 2863 (.Dup ⟨0, by decide⟩),
   pushAt 2864 1 5,
   opAt 2865 .SHR,
   pushAt 2866 1 1,
   opAt 2867 .AND,
   opAt 2868 .ISZERO,
   pushAt 2869 2 142,
   opAt 2870 .MUL,
   pushAt 2871 2 4661,
   opAt 2872 .ADD,
   opAt 2873 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
