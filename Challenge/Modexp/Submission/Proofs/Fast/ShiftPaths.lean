import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2790..2801, pc 4643..4657. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2790 .JUMPDEST,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   opAt 2792 (.Dup ⟨3, by decide⟩),
   opAt 2793 .EQ,
   pushAt 2794 0 0,
   opAt 2795 .MLOAD,
   pushAt 2796 1 255,
   opAt 2797 .SHR,
   opAt 2798 .AND,
   opAt 2799 .ISZERO,
   pushAt 2800 2 4687,
   opAt 2801 .JUMPI]

/-- Instructions 2802..2816, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2802 (.Dup ⟨0, by decide⟩),
   pushAt 2803 1 96,
   pushAt 2804 2 1024,
   opAt 2805 .CALLDATACOPY,
   opAt 2806 (.Dup ⟨0, by decide⟩),
   pushAt 2807 1 96,
   pushAt 2808 2 8256,
   opAt 2809 .CALLDATACOPY,
   pushAt 2810 0 0,
   pushAt 2811 2 8224,
   opAt 2812 .MSTORE,
   pushAt 2813 2 4692,
   pushAt 2814 2 2048,
   pushAt 2815 2 2642,
   opAt 2816 .JUMP]

/-- Instructions 2817..2819, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2817 .JUMPDEST,
   pushAt 2818 2 1533,
   opAt 2819 .JUMP]

/-- Instructions 2820..2823, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2820 .JUMPDEST,
   pushAt 2821 1 1,
   pushAt 2822 2 9408,
   opAt 2823 .MLOAD]

/-- Instructions 2824..2842, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2824 .JUMPDEST,
   opAt 2825 (.Dup ⟨0, by decide⟩),
   opAt 2826 .MLOAD,
   opAt 2827 .NOT,
   opAt 2828 (.Dup ⟨2, by decide⟩),
   opAt 2829 .ADD,
   opAt 2830 (.Dup ⟨2, by decide⟩),
   opAt 2831 (.Dup ⟨1, by decide⟩),
   opAt 2832 .LT,
   opAt 2833 (.Swap ⟨2, by decide⟩),
   opAt 2834 .POP,
   opAt 2835 (.Dup ⟨1, by decide⟩),
   pushAt 2836 2 5120,
   opAt 2837 .ADD,
   opAt 2838 .MSTORE,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 .ISZERO,
   pushAt 2841 2 4760,
   opAt 2842 .JUMPI]

/-- Instructions 2843..2846, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2843 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2844 .ADD,
   pushAt 2845 2 4699,
   opAt 2846 .JUMP]

/-- Instructions 2847..2883, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2847 .JUMPDEST,
   opAt 2848 .POP,
   opAt 2849 .POP,
   pushAt 2850 0 0,
   opAt 2851 .MLOAD,
   opAt 2852 (.Dup ⟨0, by decide⟩),
   pushAt 2853 0 0,
   opAt 2854 .SUB,
   opAt 2855 (.Dup ⟨1, by decide⟩),
   opAt 2856 .AND,
   opAt 2857 (.Dup ⟨0, by decide⟩),
   pushAt 2858 2 6144,
   opAt 2859 .MSTORE,
   opAt 2860 (.Dup ⟨0, by decide⟩),
   opAt 2861 (.Dup ⟨2, by decide⟩),
   opAt 2862 .DIV,
   opAt 2863 (.Dup ⟨0, by decide⟩),
   pushAt 2864 2 6176,
   opAt 2865 .MSTORE,
   opAt 2866 (.Dup ⟨1, by decide⟩),
   pushAt 2867 0 0,
   opAt 2868 .SUB,
   opAt 2869 (.Dup ⟨2, by decide⟩),
   opAt 2870 (.Swap ⟨0, by decide⟩),
   opAt 2871 .DIV,
   pushAt 2872 1 1,
   opAt 2873 .ADD,
   pushAt 2874 2 6208,
   opAt 2875 .MSTORE,
   opAt 2876 (.Dup ⟨0, by decide⟩),
   pushAt 2877 0 0,
   opAt 2878 .SUB,
   opAt 2879 (.Dup ⟨1, by decide⟩),
   opAt 2880 (.Swap ⟨0, by decide⟩),
   opAt 2881 .MOD,
   pushAt 2882 2 6240,
   opAt 2883 .MSTORE]

/-- Instructions 2884..2909, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2884 .JUMPDEST,
   pushAt 2885 1 1,
   opAt 2886 (.Dup ⟨0, by decide⟩),
   opAt 2887 (.Dup ⟨2, by decide⟩),
   opAt 2888 .MUL,
   pushAt 2889 1 2,
   opAt 2890 .SUB,
   opAt 2891 .MUL,
   opAt 2892 (.Dup ⟨0, by decide⟩),
   opAt 2893 (.Dup ⟨2, by decide⟩),
   opAt 2894 .MUL,
   pushAt 2895 1 2,
   opAt 2896 .SUB,
   opAt 2897 .MUL,
   opAt 2898 (.Dup ⟨0, by decide⟩),
   opAt 2899 (.Dup ⟨2, by decide⟩),
   opAt 2900 .MUL,
   pushAt 2901 1 2,
   opAt 2902 .SUB,
   opAt 2903 .MUL,
   opAt 2904 (.Dup ⟨0, by decide⟩),
   opAt 2905 (.Dup ⟨2, by decide⟩),
   opAt 2906 .MUL,
   pushAt 2907 1 2,
   opAt 2908 .SUB,
   opAt 2909 .MUL]

/-- Instructions 2910..2940, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2910 .JUMPDEST,
   opAt 2911 (.Dup ⟨0, by decide⟩),
   opAt 2912 (.Dup ⟨2, by decide⟩),
   opAt 2913 .MUL,
   pushAt 2914 1 2,
   opAt 2915 .SUB,
   opAt 2916 .MUL,
   opAt 2917 (.Dup ⟨0, by decide⟩),
   opAt 2918 (.Dup ⟨2, by decide⟩),
   opAt 2919 .MUL,
   pushAt 2920 1 2,
   opAt 2921 .SUB,
   opAt 2922 .MUL,
   opAt 2923 (.Dup ⟨0, by decide⟩),
   opAt 2924 (.Dup ⟨2, by decide⟩),
   opAt 2925 .MUL,
   pushAt 2926 1 2,
   opAt 2927 .SUB,
   opAt 2928 .MUL,
   opAt 2929 (.Dup ⟨0, by decide⟩),
   opAt 2930 (.Dup ⟨2, by decide⟩),
   opAt 2931 .MUL,
   pushAt 2932 1 2,
   opAt 2933 .SUB,
   opAt 2934 .MUL,
   pushAt 2935 2 6272,
   opAt 2936 .MSTORE,
   opAt 2937 .POP,
   opAt 2938 .POP,
   opAt 2939 .POP,
   opAt 2940 (.Dup ⟨1, by decide⟩)]

/-- Instructions 2941..2945, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2941 .JUMPDEST,
   opAt 2942 (.Dup ⟨0, by decide⟩),
   opAt 2943 .ISZERO,
   pushAt 2944 2 5366,
   opAt 2945 .JUMPI]

/-- Instructions 2946..2953, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2946 (.Dup ⟨1, by decide⟩),
   pushAt 2947 2 2048,
   pushAt 2948 2 8224,
   opAt 2949 .MCOPY,
   pushAt 2950 0 0,
   pushAt 2951 2 9440,
   opAt 2952 .MLOAD,
   opAt 2953 .MSTORE]

/-- Instructions 2954..2996, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2954 .JUMPDEST,
   pushAt 2955 2 2048,
   opAt 2956 .MLOAD,
   pushAt 2957 2 6144,
   opAt 2958 .MLOAD,
   opAt 2959 (.Dup ⟨1, by decide⟩),
   opAt 2960 (.Dup ⟨1, by decide⟩),
   opAt 2961 (.Swap ⟨0, by decide⟩),
   opAt 2962 .DIV,
   opAt 2963 (.Swap ⟨1, by decide⟩),
   opAt 2964 .MOD,
   pushAt 2965 2 6208,
   opAt 2966 .MLOAD,
   opAt 2967 .MUL,
   pushAt 2968 2 2080,
   opAt 2969 .MLOAD,
   pushAt 2970 2 6144,
   opAt 2971 .MLOAD,
   opAt 2972 (.Swap ⟨0, by decide⟩),
   opAt 2973 .DIV,
   opAt 2974 .ADD,
   pushAt 2975 2 6176,
   opAt 2976 .MLOAD,
   opAt 2977 (.Dup ⟨0, by decide⟩),
   pushAt 2978 2 6240,
   opAt 2979 .MLOAD,
   opAt 2980 (.Dup ⟨4, by decide⟩),
   opAt 2981 .MULMOD,
   opAt 2982 (.Dup ⟨2, by decide⟩),
   opAt 2983 (.Swap ⟨0, by decide⟩),
   opAt 2984 .ADDMOD,
   opAt 2985 (.Swap ⟨0, by decide⟩),
   opAt 2986 .SUB,
   pushAt 2987 2 6272,
   opAt 2988 .MLOAD,
   opAt 2989 .MUL,
   opAt 2990 (.Dup ⟨0, by decide⟩),
   opAt 2991 .ISZERO,
   opAt 2992 .ISZERO,
   opAt 2993 (.Swap ⟨0, by decide⟩),
   opAt 2994 .SUB,
   opAt 2995 (.Swap ⟨0, by decide⟩),
   opAt 2996 .POP]

/-- Instructions 2997..3004, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2997 .JUMPDEST,
   pushAt 2998 0 0,
   pushAt 2999 2 9440,
   opAt 3000 .MLOAD,
   pushAt 3001 2 9408,
   opAt 3002 .MLOAD,
   pushAt 3003 2 5120,
   opAt 3004 .ADD]

/-- Instructions 3005..3052, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3005 .JUMPDEST,
   opAt 3006 (.Dup ⟨3, by decide⟩),
   opAt 3007 (.Dup ⟨1, by decide⟩),
   opAt 3008 .MLOAD,
   opAt 3009 (.Dup ⟨1, by decide⟩),
   opAt 3010 (.Dup ⟨1, by decide⟩),
   opAt 3011 .MUL,
   opAt 3012 (.Swap ⟨1, by decide⟩),
   pushAt 3013 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3014 (.Swap ⟨1, by decide⟩),
   opAt 3015 .MULMOD,
   opAt 3016 (.Dup ⟨1, by decide⟩),
   opAt 3017 (.Dup ⟨1, by decide⟩),
   opAt 3018 .LT,
   opAt 3019 (.Dup ⟨2, by decide⟩),
   opAt 3020 .ADD,
   opAt 3021 (.Swap ⟨0, by decide⟩),
   opAt 3022 .SUB,
   opAt 3023 (.Dup ⟨3, by decide⟩),
   opAt 3024 .MLOAD,
   opAt 3025 (.Swap ⟨1, by decide⟩),
   opAt 3026 (.Dup ⟨2, by decide⟩),
   opAt 3027 .ADD,
   opAt 3028 (.Swap ⟨1, by decide⟩),
   opAt 3029 (.Dup ⟨2, by decide⟩),
   opAt 3030 .LT,
   opAt 3031 .ADD,
   opAt 3032 (.Swap ⟨0, by decide⟩),
   opAt 3033 (.Dup ⟨4, by decide⟩),
   opAt 3034 .ADD,
   opAt 3035 (.Swap ⟨3, by decide⟩),
   opAt 3036 (.Dup ⟨4, by decide⟩),
   opAt 3037 .LT,
   opAt 3038 .ADD,
   opAt 3039 (.Swap ⟨2, by decide⟩),
   opAt 3040 (.Dup ⟨2, by decide⟩),
   opAt 3041 .MSTORE,
   pushAt 3042 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3043 .ADD,
   opAt 3044 (.Swap ⟨0, by decide⟩),
   pushAt 3045 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3046 .ADD,
   opAt 3047 (.Swap ⟨0, by decide⟩),
   pushAt 3048 2 8224,
   opAt 3049 (.Dup ⟨2, by decide⟩),
   opAt 3050 .GT,
   pushAt 3051 2 4968,
   opAt 3052 .JUMPI]

/-- Instructions 3053..3080, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3053 .POP,
   opAt 3054 .POP,
   pushAt 3055 2 8224,
   opAt 3056 .MLOAD,
   opAt 3057 (.Dup ⟨1, by decide⟩),
   opAt 3058 .ADD,
   opAt 3059 (.Dup ⟨1, by decide⟩),
   opAt 3060 (.Dup ⟨1, by decide⟩),
   opAt 3061 .LT,
   opAt 3062 (.Swap ⟨1, by decide⟩),
   opAt 3063 .POP,
   opAt 3064 (.Dup ⟨2, by decide⟩),
   opAt 3065 (.Dup ⟨1, by decide⟩),
   opAt 3066 .LT,
   opAt 3067 (.Swap ⟨0, by decide⟩),
   opAt 3068 (.Dup ⟨3, by decide⟩),
   opAt 3069 (.Swap ⟨0, by decide⟩),
   opAt 3070 .SUB,
   opAt 3071 (.Dup ⟨0, by decide⟩),
   pushAt 3072 2 8224,
   opAt 3073 .MSTORE,
   opAt 3074 .POP,
   opAt 3075 .GT,
   opAt 3076 (.Swap ⟨0, by decide⟩),
   opAt 3077 .POP,
   opAt 3078 .ISZERO,
   pushAt 3079 2 5247,
   opAt 3080 .JUMPI]

/-- Instructions 3081..3084, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3081 .JUMPDEST,
   pushAt 3082 0 0,
   pushAt 3083 2 9440,
   opAt 3084 .MLOAD]

/-- Instructions 3085..3119, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3085 .JUMPDEST,
   opAt 3086 (.Dup ⟨0, by decide⟩),
   opAt 3087 .MLOAD,
   opAt 3088 (.Dup ⟨1, by decide⟩),
   pushAt 3089 2 8256,
   opAt 3090 (.Swap ⟨0, by decide⟩),
   opAt 3091 .SUB,
   opAt 3092 .MLOAD,
   opAt 3093 (.Dup ⟨1, by decide⟩),
   opAt 3094 .ADD,
   opAt 3095 (.Dup ⟨0, by decide⟩),
   opAt 3096 (.Dup ⟨2, by decide⟩),
   opAt 3097 .GT,
   opAt 3098 (.Swap ⟨1, by decide⟩),
   opAt 3099 .POP,
   opAt 3100 (.Dup ⟨3, by decide⟩),
   opAt 3101 .ADD,
   opAt 3102 (.Dup ⟨0, by decide⟩),
   opAt 3103 (.Dup ⟨4, by decide⟩),
   opAt 3104 .GT,
   opAt 3105 (.Swap ⟨3, by decide⟩),
   opAt 3106 .POP,
   opAt 3107 (.Dup ⟨2, by decide⟩),
   opAt 3108 .MSTORE,
   opAt 3109 (.Swap ⟨0, by decide⟩),
   opAt 3110 (.Swap ⟨1, by decide⟩),
   opAt 3111 .OR,
   opAt 3112 (.Swap ⟨0, by decide⟩),
   pushAt 3113 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3114 .ADD,
   pushAt 3115 2 8255,
   opAt 3116 (.Dup ⟨1, by decide⟩),
   opAt 3117 .GT,
   pushAt 3118 2 5156,
   opAt 3119 .JUMPI]

/-- Instructions 3120..3131, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3120 .POP,
   pushAt 3121 2 8224,
   opAt 3122 .MLOAD,
   opAt 3123 (.Dup ⟨1, by decide⟩),
   opAt 3124 .ADD,
   opAt 3125 (.Dup ⟨0, by decide⟩),
   pushAt 3126 2 8224,
   opAt 3127 .MSTORE,
   opAt 3128 .LT,
   opAt 3129 .ISZERO,
   pushAt 3130 2 5150,
   opAt 3131 .JUMPI]

/-- Instructions 3132..3137, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3132 .JUMPDEST,
   pushAt 3133 2 8224,
   opAt 3134 .MLOAD,
   opAt 3135 .ISZERO,
   pushAt 3136 2 5346,
   opAt 3137 .JUMPI]

/-- Instructions 3138..3140, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3138 0 0,
   pushAt 3139 2 9440,
   opAt 3140 .MLOAD]

/-- Instructions 3141..3172, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3141 .JUMPDEST,
   opAt 3142 (.Dup ⟨0, by decide⟩),
   opAt 3143 .MLOAD,
   opAt 3144 (.Dup ⟨1, by decide⟩),
   pushAt 3145 2 8256,
   opAt 3146 (.Swap ⟨0, by decide⟩),
   opAt 3147 .SUB,
   opAt 3148 .MLOAD,
   opAt 3149 (.Dup ⟨1, by decide⟩),
   opAt 3150 (.Dup ⟨1, by decide⟩),
   opAt 3151 .GT,
   opAt 3152 (.Swap ⟨1, by decide⟩),
   opAt 3153 .SUB,
   opAt 3154 (.Dup ⟨3, by decide⟩),
   opAt 3155 (.Dup ⟨1, by decide⟩),
   opAt 3156 .LT,
   opAt 3157 (.Swap ⟨0, by decide⟩),
   opAt 3158 (.Dup ⟨4, by decide⟩),
   opAt 3159 (.Swap ⟨0, by decide⟩),
   opAt 3160 .SUB,
   opAt 3161 (.Dup ⟨3, by decide⟩),
   opAt 3162 .MSTORE,
   opAt 3163 .OR,
   opAt 3164 (.Swap ⟨1, by decide⟩),
   opAt 3165 .POP,
   pushAt 3166 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3167 .ADD,
   pushAt 3168 2 8255,
   opAt 3169 (.Dup ⟨1, by decide⟩),
   opAt 3170 .GT,
   pushAt 3171 2 5262,
   opAt 3172 .JUMPI]

/-- Instructions 3173..3180, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3173 .POP,
   pushAt 3174 2 8224,
   opAt 3175 .MLOAD,
   opAt 3176 .SUB,
   pushAt 3177 2 8224,
   opAt 3178 .MSTORE,
   pushAt 3179 2 5247,
   opAt 3180 .JUMP]

/-- Instructions 3181..3185, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3181 .JUMPDEST,
   pushAt 3182 2 5357,
   pushAt 3183 2 2048,
   pushAt 3184 2 2642,
   opAt 3185 .JUMP]

/-- Instructions 3186..3191, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3186 .JUMPDEST,
   pushAt 3187 1 1,
   opAt 3188 (.Swap ⟨0, by decide⟩),
   opAt 3189 .SUB,
   pushAt 3190 2 4874,
   opAt 3191 .JUMP]

/-- Instructions 3192..3195, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3192 .JUMPDEST,
   opAt 3193 .POP,
   pushAt 3194 2 1756,
   opAt 3195 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4643 = true :=
  Artifact.isValidJumpDest_index 2790 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4687 = true :=
  Artifact.isValidJumpDest_index 2817 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4692 = true :=
  Artifact.isValidJumpDest_index 2820 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4699 = true :=
  Artifact.isValidJumpDest_index 2824 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4760 = true :=
  Artifact.isValidJumpDest_index 2847 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4806 = true :=
  Artifact.isValidJumpDest_index 2884 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4837 = true :=
  Artifact.isValidJumpDest_index 2910 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4874 = true :=
  Artifact.isValidJumpDest_index 2941 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4895 = true :=
  Artifact.isValidJumpDest_index 2954 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4954 = true :=
  Artifact.isValidJumpDest_index 2997 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4968 = true :=
  Artifact.isValidJumpDest_index 3005 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5150 = true :=
  Artifact.isValidJumpDest_index 3081 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5156 = true :=
  Artifact.isValidJumpDest_index 3085 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5247 = true :=
  Artifact.isValidJumpDest_index 3132 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5262 = true :=
  Artifact.isValidJumpDest_index 3141 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5346 = true :=
  Artifact.isValidJumpDest_index 3181 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5357 = true :=
  Artifact.isValidJumpDest_index 3186 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5366 = true :=
  Artifact.isValidJumpDest_index 3192 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
