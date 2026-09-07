import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2862..2873, pc 4643..4657. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2862 .JUMPDEST,
   opAt 2863 (.Dup ⟨0, by decide⟩),
   opAt 2864 (.Dup ⟨3, by decide⟩),
   opAt 2865 .EQ,
   pushAt 2866 0 0,
   opAt 2867 .MLOAD,
   pushAt 2868 1 255,
   opAt 2869 .SHR,
   opAt 2870 .AND,
   opAt 2871 .ISZERO,
   pushAt 2872 2 4687,
   opAt 2873 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2874 (.Dup ⟨0, by decide⟩),
   pushAt 2875 1 96,
   pushAt 2876 2 1024,
   opAt 2877 .CALLDATACOPY,
   opAt 2878 (.Dup ⟨0, by decide⟩),
   pushAt 2879 1 96,
   pushAt 2880 2 8256,
   opAt 2881 .CALLDATACOPY,
   pushAt 2882 0 0,
   pushAt 2883 2 8224,
   opAt 2884 .MSTORE,
   pushAt 2885 2 4692,
   pushAt 2886 2 2048,
   pushAt 2887 2 2642,
   opAt 2888 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2889 .JUMPDEST,
   pushAt 2890 2 1533,
   opAt 2891 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2892 .JUMPDEST,
   pushAt 2893 1 1,
   pushAt 2894 2 9408,
   opAt 2895 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2896 .JUMPDEST,
   opAt 2897 (.Dup ⟨0, by decide⟩),
   opAt 2898 .MLOAD,
   opAt 2899 .NOT,
   opAt 2900 (.Dup ⟨2, by decide⟩),
   opAt 2901 .ADD,
   opAt 2902 (.Dup ⟨2, by decide⟩),
   opAt 2903 (.Dup ⟨1, by decide⟩),
   opAt 2904 .LT,
   opAt 2905 (.Swap ⟨2, by decide⟩),
   opAt 2906 .POP,
   opAt 2907 (.Dup ⟨1, by decide⟩),
   pushAt 2908 2 5120,
   opAt 2909 .ADD,
   opAt 2910 .MSTORE,
   opAt 2911 (.Dup ⟨0, by decide⟩),
   opAt 2912 .ISZERO,
   pushAt 2913 2 4760,
   opAt 2914 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2915 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2916 .ADD,
   pushAt 2917 2 4699,
   opAt 2918 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2919 .JUMPDEST,
   opAt 2920 .POP,
   opAt 2921 .POP,
   pushAt 2922 0 0,
   opAt 2923 .MLOAD,
   opAt 2924 (.Dup ⟨0, by decide⟩),
   pushAt 2925 0 0,
   opAt 2926 .SUB,
   opAt 2927 (.Dup ⟨1, by decide⟩),
   opAt 2928 .AND,
   opAt 2929 (.Dup ⟨0, by decide⟩),
   pushAt 2930 2 6144,
   opAt 2931 .MSTORE,
   opAt 2932 (.Dup ⟨0, by decide⟩),
   opAt 2933 (.Dup ⟨2, by decide⟩),
   opAt 2934 .DIV,
   opAt 2935 (.Dup ⟨0, by decide⟩),
   pushAt 2936 2 6176,
   opAt 2937 .MSTORE,
   opAt 2938 (.Dup ⟨1, by decide⟩),
   pushAt 2939 0 0,
   opAt 2940 .SUB,
   opAt 2941 (.Dup ⟨2, by decide⟩),
   opAt 2942 (.Swap ⟨0, by decide⟩),
   opAt 2943 .DIV,
   pushAt 2944 1 1,
   opAt 2945 .ADD,
   pushAt 2946 2 6208,
   opAt 2947 .MSTORE,
   opAt 2948 (.Dup ⟨0, by decide⟩),
   pushAt 2949 0 0,
   opAt 2950 .SUB,
   opAt 2951 (.Dup ⟨1, by decide⟩),
   opAt 2952 (.Swap ⟨0, by decide⟩),
   opAt 2953 .MOD,
   pushAt 2954 2 6240,
   opAt 2955 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2956 .JUMPDEST,
   pushAt 2957 1 1,
   opAt 2958 (.Dup ⟨0, by decide⟩),
   opAt 2959 (.Dup ⟨2, by decide⟩),
   opAt 2960 .MUL,
   pushAt 2961 1 2,
   opAt 2962 .SUB,
   opAt 2963 .MUL,
   opAt 2964 (.Dup ⟨0, by decide⟩),
   opAt 2965 (.Dup ⟨2, by decide⟩),
   opAt 2966 .MUL,
   pushAt 2967 1 2,
   opAt 2968 .SUB,
   opAt 2969 .MUL,
   opAt 2970 (.Dup ⟨0, by decide⟩),
   opAt 2971 (.Dup ⟨2, by decide⟩),
   opAt 2972 .MUL,
   pushAt 2973 1 2,
   opAt 2974 .SUB,
   opAt 2975 .MUL,
   opAt 2976 (.Dup ⟨0, by decide⟩),
   opAt 2977 (.Dup ⟨2, by decide⟩),
   opAt 2978 .MUL,
   pushAt 2979 1 2,
   opAt 2980 .SUB,
   opAt 2981 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2982 .JUMPDEST,
   opAt 2983 (.Dup ⟨0, by decide⟩),
   opAt 2984 (.Dup ⟨2, by decide⟩),
   opAt 2985 .MUL,
   pushAt 2986 1 2,
   opAt 2987 .SUB,
   opAt 2988 .MUL,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   opAt 2990 (.Dup ⟨2, by decide⟩),
   opAt 2991 .MUL,
   pushAt 2992 1 2,
   opAt 2993 .SUB,
   opAt 2994 .MUL,
   opAt 2995 (.Dup ⟨0, by decide⟩),
   opAt 2996 (.Dup ⟨2, by decide⟩),
   opAt 2997 .MUL,
   pushAt 2998 1 2,
   opAt 2999 .SUB,
   opAt 3000 .MUL,
   opAt 3001 (.Dup ⟨0, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   opAt 3003 .MUL,
   pushAt 3004 1 2,
   opAt 3005 .SUB,
   opAt 3006 .MUL,
   pushAt 3007 2 6272,
   opAt 3008 .MSTORE,
   opAt 3009 .POP,
   opAt 3010 .POP,
   opAt 3011 .POP,
   opAt 3012 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3013 .JUMPDEST,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   opAt 3015 .ISZERO,
   pushAt 3016 2 5366,
   opAt 3017 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3018 (.Dup ⟨1, by decide⟩),
   pushAt 3019 2 2048,
   pushAt 3020 2 8224,
   opAt 3021 .MCOPY,
   pushAt 3022 0 0,
   pushAt 3023 2 9440,
   opAt 3024 .MLOAD,
   opAt 3025 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3026 .JUMPDEST,
   pushAt 3027 2 2048,
   opAt 3028 .MLOAD,
   pushAt 3029 2 6144,
   opAt 3030 .MLOAD,
   opAt 3031 (.Dup ⟨1, by decide⟩),
   opAt 3032 (.Dup ⟨1, by decide⟩),
   opAt 3033 (.Swap ⟨0, by decide⟩),
   opAt 3034 .DIV,
   opAt 3035 (.Swap ⟨1, by decide⟩),
   opAt 3036 .MOD,
   pushAt 3037 2 6208,
   opAt 3038 .MLOAD,
   opAt 3039 .MUL,
   pushAt 3040 2 2080,
   opAt 3041 .MLOAD,
   pushAt 3042 2 6144,
   opAt 3043 .MLOAD,
   opAt 3044 (.Swap ⟨0, by decide⟩),
   opAt 3045 .DIV,
   opAt 3046 .ADD,
   pushAt 3047 2 6176,
   opAt 3048 .MLOAD,
   opAt 3049 (.Dup ⟨0, by decide⟩),
   pushAt 3050 2 6240,
   opAt 3051 .MLOAD,
   opAt 3052 (.Dup ⟨4, by decide⟩),
   opAt 3053 .MULMOD,
   opAt 3054 (.Dup ⟨2, by decide⟩),
   opAt 3055 (.Swap ⟨0, by decide⟩),
   opAt 3056 .ADDMOD,
   opAt 3057 (.Swap ⟨0, by decide⟩),
   opAt 3058 .SUB,
   pushAt 3059 2 6272,
   opAt 3060 .MLOAD,
   opAt 3061 .MUL,
   opAt 3062 (.Dup ⟨0, by decide⟩),
   opAt 3063 .ISZERO,
   opAt 3064 .ISZERO,
   opAt 3065 (.Swap ⟨0, by decide⟩),
   opAt 3066 .SUB,
   opAt 3067 (.Swap ⟨0, by decide⟩),
   opAt 3068 .POP]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3069 .JUMPDEST,
   pushAt 3070 0 0,
   pushAt 3071 2 9440,
   opAt 3072 .MLOAD,
   pushAt 3073 2 9408,
   opAt 3074 .MLOAD,
   pushAt 3075 2 5120,
   opAt 3076 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3077 .JUMPDEST,
   opAt 3078 (.Dup ⟨3, by decide⟩),
   opAt 3079 (.Dup ⟨1, by decide⟩),
   opAt 3080 .MLOAD,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 (.Dup ⟨1, by decide⟩),
   opAt 3083 .MUL,
   opAt 3084 (.Swap ⟨1, by decide⟩),
   pushAt 3085 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3086 (.Swap ⟨1, by decide⟩),
   opAt 3087 .MULMOD,
   opAt 3088 (.Dup ⟨1, by decide⟩),
   opAt 3089 (.Dup ⟨1, by decide⟩),
   opAt 3090 .LT,
   opAt 3091 (.Dup ⟨2, by decide⟩),
   opAt 3092 .ADD,
   opAt 3093 (.Swap ⟨0, by decide⟩),
   opAt 3094 .SUB,
   opAt 3095 (.Dup ⟨3, by decide⟩),
   opAt 3096 .MLOAD,
   opAt 3097 (.Swap ⟨1, by decide⟩),
   opAt 3098 (.Dup ⟨2, by decide⟩),
   opAt 3099 .ADD,
   opAt 3100 (.Swap ⟨1, by decide⟩),
   opAt 3101 (.Dup ⟨2, by decide⟩),
   opAt 3102 .LT,
   opAt 3103 .ADD,
   opAt 3104 (.Swap ⟨0, by decide⟩),
   opAt 3105 (.Dup ⟨4, by decide⟩),
   opAt 3106 .ADD,
   opAt 3107 (.Swap ⟨3, by decide⟩),
   opAt 3108 (.Dup ⟨4, by decide⟩),
   opAt 3109 .LT,
   opAt 3110 .ADD,
   opAt 3111 (.Swap ⟨2, by decide⟩),
   opAt 3112 (.Dup ⟨2, by decide⟩),
   opAt 3113 .MSTORE,
   pushAt 3114 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3115 .ADD,
   opAt 3116 (.Swap ⟨0, by decide⟩),
   pushAt 3117 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3118 .ADD,
   opAt 3119 (.Swap ⟨0, by decide⟩),
   pushAt 3120 2 8224,
   opAt 3121 (.Dup ⟨2, by decide⟩),
   opAt 3122 .GT,
   pushAt 3123 2 4968,
   opAt 3124 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3125 .POP,
   opAt 3126 .POP,
   pushAt 3127 2 8224,
   opAt 3128 .MLOAD,
   opAt 3129 (.Dup ⟨1, by decide⟩),
   opAt 3130 .ADD,
   opAt 3131 (.Dup ⟨1, by decide⟩),
   opAt 3132 (.Dup ⟨1, by decide⟩),
   opAt 3133 .LT,
   opAt 3134 (.Swap ⟨1, by decide⟩),
   opAt 3135 .POP,
   opAt 3136 (.Dup ⟨2, by decide⟩),
   opAt 3137 (.Dup ⟨1, by decide⟩),
   opAt 3138 .LT,
   opAt 3139 (.Swap ⟨0, by decide⟩),
   opAt 3140 (.Dup ⟨3, by decide⟩),
   opAt 3141 (.Swap ⟨0, by decide⟩),
   opAt 3142 .SUB,
   opAt 3143 (.Dup ⟨0, by decide⟩),
   pushAt 3144 2 8224,
   opAt 3145 .MSTORE,
   opAt 3146 .POP,
   opAt 3147 .GT,
   opAt 3148 (.Swap ⟨0, by decide⟩),
   opAt 3149 .POP,
   opAt 3150 .ISZERO,
   pushAt 3151 2 5247,
   opAt 3152 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3153 .JUMPDEST,
   pushAt 3154 0 0,
   pushAt 3155 2 9440,
   opAt 3156 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3157 .JUMPDEST,
   opAt 3158 (.Dup ⟨0, by decide⟩),
   opAt 3159 .MLOAD,
   opAt 3160 (.Dup ⟨1, by decide⟩),
   pushAt 3161 2 8256,
   opAt 3162 (.Swap ⟨0, by decide⟩),
   opAt 3163 .SUB,
   opAt 3164 .MLOAD,
   opAt 3165 (.Dup ⟨1, by decide⟩),
   opAt 3166 .ADD,
   opAt 3167 (.Dup ⟨0, by decide⟩),
   opAt 3168 (.Dup ⟨2, by decide⟩),
   opAt 3169 .GT,
   opAt 3170 (.Swap ⟨1, by decide⟩),
   opAt 3171 .POP,
   opAt 3172 (.Dup ⟨3, by decide⟩),
   opAt 3173 .ADD,
   opAt 3174 (.Dup ⟨0, by decide⟩),
   opAt 3175 (.Dup ⟨4, by decide⟩),
   opAt 3176 .GT,
   opAt 3177 (.Swap ⟨3, by decide⟩),
   opAt 3178 .POP,
   opAt 3179 (.Dup ⟨2, by decide⟩),
   opAt 3180 .MSTORE,
   opAt 3181 (.Swap ⟨0, by decide⟩),
   opAt 3182 (.Swap ⟨1, by decide⟩),
   opAt 3183 .OR,
   opAt 3184 (.Swap ⟨0, by decide⟩),
   pushAt 3185 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3186 .ADD,
   pushAt 3187 2 8255,
   opAt 3188 (.Dup ⟨1, by decide⟩),
   opAt 3189 .GT,
   pushAt 3190 2 5156,
   opAt 3191 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3192 .POP,
   pushAt 3193 2 8224,
   opAt 3194 .MLOAD,
   opAt 3195 (.Dup ⟨1, by decide⟩),
   opAt 3196 .ADD,
   opAt 3197 (.Dup ⟨0, by decide⟩),
   pushAt 3198 2 8224,
   opAt 3199 .MSTORE,
   opAt 3200 .LT,
   opAt 3201 .ISZERO,
   pushAt 3202 2 5150,
   opAt 3203 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3204 .JUMPDEST,
   pushAt 3205 2 8224,
   opAt 3206 .MLOAD,
   opAt 3207 .ISZERO,
   pushAt 3208 2 5346,
   opAt 3209 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3210 0 0,
   pushAt 3211 2 9440,
   opAt 3212 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3213 .JUMPDEST,
   opAt 3214 (.Dup ⟨0, by decide⟩),
   opAt 3215 .MLOAD,
   opAt 3216 (.Dup ⟨1, by decide⟩),
   pushAt 3217 2 8256,
   opAt 3218 (.Swap ⟨0, by decide⟩),
   opAt 3219 .SUB,
   opAt 3220 .MLOAD,
   opAt 3221 (.Dup ⟨1, by decide⟩),
   opAt 3222 (.Dup ⟨1, by decide⟩),
   opAt 3223 .GT,
   opAt 3224 (.Swap ⟨1, by decide⟩),
   opAt 3225 .SUB,
   opAt 3226 (.Dup ⟨3, by decide⟩),
   opAt 3227 (.Dup ⟨1, by decide⟩),
   opAt 3228 .LT,
   opAt 3229 (.Swap ⟨0, by decide⟩),
   opAt 3230 (.Dup ⟨4, by decide⟩),
   opAt 3231 (.Swap ⟨0, by decide⟩),
   opAt 3232 .SUB,
   opAt 3233 (.Dup ⟨3, by decide⟩),
   opAt 3234 .MSTORE,
   opAt 3235 .OR,
   opAt 3236 (.Swap ⟨1, by decide⟩),
   opAt 3237 .POP,
   pushAt 3238 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3239 .ADD,
   pushAt 3240 2 8255,
   opAt 3241 (.Dup ⟨1, by decide⟩),
   opAt 3242 .GT,
   pushAt 3243 2 5262,
   opAt 3244 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3245 .POP,
   pushAt 3246 2 8224,
   opAt 3247 .MLOAD,
   opAt 3248 .SUB,
   pushAt 3249 2 8224,
   opAt 3250 .MSTORE,
   pushAt 3251 2 5247,
   opAt 3252 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3253 .JUMPDEST,
   pushAt 3254 2 5357,
   pushAt 3255 2 2048,
   pushAt 3256 2 2642,
   opAt 3257 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3258 .JUMPDEST,
   pushAt 3259 1 1,
   opAt 3260 (.Swap ⟨0, by decide⟩),
   opAt 3261 .SUB,
   pushAt 3262 2 4874,
   opAt 3263 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3264 .JUMPDEST,
   opAt 3265 .POP,
   pushAt 3266 2 1756,
   opAt 3267 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4643 = true :=
  Artifact.isValidJumpDest_index 2862 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4687 = true :=
  Artifact.isValidJumpDest_index 2889 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4692 = true :=
  Artifact.isValidJumpDest_index 2892 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4699 = true :=
  Artifact.isValidJumpDest_index 2896 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4760 = true :=
  Artifact.isValidJumpDest_index 2919 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4806 = true :=
  Artifact.isValidJumpDest_index 2956 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4837 = true :=
  Artifact.isValidJumpDest_index 2982 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4874 = true :=
  Artifact.isValidJumpDest_index 3013 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4895 = true :=
  Artifact.isValidJumpDest_index 3026 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4954 = true :=
  Artifact.isValidJumpDest_index 3069 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4968 = true :=
  Artifact.isValidJumpDest_index 3077 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5150 = true :=
  Artifact.isValidJumpDest_index 3153 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5156 = true :=
  Artifact.isValidJumpDest_index 3157 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5247 = true :=
  Artifact.isValidJumpDest_index 3204 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5262 = true :=
  Artifact.isValidJumpDest_index 3213 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5346 = true :=
  Artifact.isValidJumpDest_index 3253 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5357 = true :=
  Artifact.isValidJumpDest_index 3258 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5366 = true :=
  Artifact.isValidJumpDest_index 3264 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
