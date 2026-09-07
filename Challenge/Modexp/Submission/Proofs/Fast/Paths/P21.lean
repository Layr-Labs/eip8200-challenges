import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Located paths for the appended fused `ADDMOD`/conditional-subtract routine. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Fused routine entry, instructions 2862..2877, pc 4643..4664. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2862 .JUMPDEST,
   pushAt 2863 2 8256,
   opAt 2864 (.Dup ⟨1, by decide⟩),
   opAt 2865 .SUB,
   pushAt 2866 2 8256,
   opAt 2867 (.Dup ⟨3, by decide⟩),
   opAt 2868 .SUB,
   opAt 2869 (.Swap ⟨0, by decide⟩),
   opAt 2870 (.Swap ⟨1, by decide⟩),
   opAt 2871 .POP,
   opAt 2872 (.Swap ⟨1, by decide⟩),
   opAt 2873 .POP,
   pushAt 2874 0 0,
   pushAt 2875 0 0,
   pushAt 2876 2 9440,
   opAt 2877 .MLOAD]

/-- Fused limb loop, instructions 2878..2932, pc 4665..4728. -/
def blk2878 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2878 .JUMPDEST,
   opAt 2879 (.Dup ⟨3, by decide⟩),
   opAt 2880 (.Dup ⟨1, by decide⟩),
   opAt 2881 .ADD,
   opAt 2882 .MLOAD,
   opAt 2883 (.Dup ⟨5, by decide⟩),
   opAt 2884 (.Dup ⟨2, by decide⟩),
   opAt 2885 .ADD,
   opAt 2886 .MLOAD,
   opAt 2887 (.Dup ⟨1, by decide⟩),
   opAt 2888 .ADD,
   opAt 2889 (.Dup ⟨0, by decide⟩),
   opAt 2890 (.Swap ⟨1, by decide⟩),
   opAt 2891 .GT,
   opAt 2892 (.Dup ⟨3, by decide⟩),
   opAt 2893 (.Dup ⟨2, by decide⟩),
   opAt 2894 .ADD,
   opAt 2895 (.Dup ⟨0, by decide⟩),
   opAt 2896 (.Swap ⟨2, by decide⟩),
   opAt 2897 .GT,
   opAt 2898 .OR,
   opAt 2899 (.Swap ⟨2, by decide⟩),
   opAt 2900 .POP,
   pushAt 2901 2 8256,
   opAt 2902 (.Dup ⟨2, by decide⟩),
   opAt 2903 .SUB,
   opAt 2904 .MLOAD,
   opAt 2905 (.Dup ⟨1, by decide⟩),
   opAt 2906 .SUB,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 (.Dup ⟨2, by decide⟩),
   opAt 2909 .LT,
   opAt 2910 (.Dup ⟨5, by decide⟩),
   opAt 2911 (.Dup ⟨2, by decide⟩),
   opAt 2912 .SUB,
   opAt 2913 (.Dup ⟨0, by decide⟩),
   opAt 2914 (.Swap ⟨2, by decide⟩),
   opAt 2915 .LT,
   opAt 2916 .OR,
   opAt 2917 (.Swap ⟨4, by decide⟩),
   opAt 2918 .POP,
   pushAt 2919 2 1088,
   opAt 2920 (.Dup ⟨3, by decide⟩),
   opAt 2921 .SUB,
   opAt 2922 .MSTORE,
   opAt 2923 (.Dup ⟨1, by decide⟩),
   opAt 2924 .MSTORE,
   pushAt 2925 1 32,
   opAt 2926 (.Swap ⟨0, by decide⟩),
   opAt 2927 .SUB,
   pushAt 2928 2 8224,
   opAt 2929 (.Dup ⟨1, by decide⟩),
   opAt 2930 .GT,
   pushAt 2931 2 4665,
   opAt 2932 .JUMPI]

/-- Fused selection and return, instructions 2933..2955, pc 4729..4759. -/
def blk2933 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2933 (.Dup ⟨1, by decide⟩),
   pushAt 2934 2 8224,
   opAt 2935 .MSTORE,
   opAt 2936 (.Dup ⟨2, by decide⟩),
   opAt 2937 .ISZERO,
   opAt 2938 (.Dup ⟨2, by decide⟩),
   opAt 2939 .OR,
   pushAt 2940 2 1088,
   opAt 2941 .MUL,
   pushAt 2942 2 8256,
   opAt 2943 .SUB,
   pushAt 2944 2 9344,
   opAt 2945 .MLOAD,
   opAt 2946 (.Swap ⟨0, by decide⟩),
   opAt 2947 (.Dup ⟨7, by decide⟩),
   opAt 2948 .MCOPY,
   opAt 2949 .POP,
   opAt 2950 .POP,
   opAt 2951 .POP,
   opAt 2952 .POP,
   opAt 2953 .POP,
   opAt 2954 .POP,
   opAt 2955 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
