import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2500..2511, pc 3841..4913. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2776 .JUMPDEST,
   opAt 2777 (.Dup ⟨0, by decide⟩),
   opAt 2778 (.Dup ⟨3, by decide⟩),
   opAt 2779 .EQ,
   pushAt 2780 0 0,
   opAt 2781 .MLOAD,
   pushAt 2782 1 255,
   opAt 2783 .SHR,
   opAt 2784 .AND,
   opAt 2785 .ISZERO,
   pushAt 2786 2 3860,
   opAt 2787 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2788 (.Dup ⟨0, by decide⟩),
   pushAt 2789 1 96,
   pushAt 2790 2 1024,
   opAt 2791 .CALLDATACOPY,
   opAt 2792 (.Dup ⟨0, by decide⟩),
   pushAt 2793 1 96,
   pushAt 2794 2 8256,
   opAt 2795 .CALLDATACOPY,
   pushAt 2796 0 0,
   pushAt 2797 2 8224,
   opAt 2798 .MSTORE,
   pushAt 2799 2 3865,
   pushAt 2800 2 2048,
   pushAt 2801 2 2304,
   opAt 2802 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2803 .JUMPDEST,
   pushAt 2804 2 1533,
   opAt 2805 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2806 .JUMPDEST,
   pushAt 2807 1 1,
   pushAt 2808 2 9408,
   opAt 2809 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2810 .JUMPDEST,
   opAt 2811 (.Dup ⟨0, by decide⟩),
   opAt 2812 .MLOAD,
   opAt 2813 .NOT,
   opAt 2814 (.Dup ⟨2, by decide⟩),
   opAt 2815 .ADD,
   opAt 2816 (.Dup ⟨2, by decide⟩),
   opAt 2817 (.Dup ⟨1, by decide⟩),
   opAt 2818 .LT,
   opAt 2819 (.Swap ⟨2, by decide⟩),
   opAt 2820 .POP,
   opAt 2821 (.Dup ⟨1, by decide⟩),
   pushAt 2822 2 5120,
   opAt 2823 .ADD,
   opAt 2824 .MSTORE,
   opAt 2825 (.Dup ⟨0, by decide⟩),
   opAt 2826 .ISZERO,
   pushAt 2827 2 3903,
   opAt 2828 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2829 1 31, opAt 2830 .NOT,
   opAt 2831 .ADD,
   pushAt 2832 2 3872,
   opAt 2833 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2834 .JUMPDEST,
   opAt 2835 .POP,
   opAt 2836 .POP,
   pushAt 2837 0 0,
   opAt 2838 .MLOAD,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   pushAt 2840 0 0,
   opAt 2841 .SUB,
   opAt 2842 (.Dup ⟨1, by decide⟩),
   opAt 2843 .AND,
   opAt 2844 (.Dup ⟨0, by decide⟩),
   pushAt 2845 2 6144,
   opAt 2846 .MSTORE,
   opAt 2847 (.Dup ⟨0, by decide⟩),
   opAt 2848 (.Dup ⟨2, by decide⟩),
   opAt 2849 .DIV,
   opAt 2850 (.Dup ⟨0, by decide⟩),
   pushAt 2851 2 6176,
   opAt 2852 .MSTORE,
   opAt 2853 (.Dup ⟨1, by decide⟩),
   pushAt 2854 0 0,
   opAt 2855 .SUB,
   opAt 2856 (.Dup ⟨2, by decide⟩),
   opAt 2857 (.Swap ⟨0, by decide⟩),
   opAt 2858 .DIV,
   pushAt 2859 1 1,
   opAt 2860 .ADD,
   pushAt 2861 2 6208,
   opAt 2862 .MSTORE,
   opAt 2863 (.Dup ⟨0, by decide⟩),
   pushAt 2864 0 0,
   opAt 2865 .SUB,
   opAt 2866 (.Dup ⟨1, by decide⟩),
   opAt 2867 (.Swap ⟨0, by decide⟩),
   opAt 2868 .MOD,
   pushAt 2869 2 6240,
   opAt 2870 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2871 .JUMPDEST,
   opAt 2872 (.Dup ⟨0, by decide⟩),
   pushAt 2873 2 2,
   opAt 2874 .SUB,
   opAt 2875 .JUMPDEST,
   opAt 2876 .JUMPDEST,
   opAt 2877 .JUMPDEST,
   opAt 2878 .JUMPDEST,
   opAt 2879 (.Dup ⟨0, by decide⟩),
   opAt 2880 (.Dup ⟨2, by decide⟩),
   opAt 2881 .MUL,
   pushAt 2882 1 2,
   opAt 2883 .SUB,
   opAt 2884 .MUL,
   opAt 2885 (.Dup ⟨0, by decide⟩),
   opAt 2886 (.Dup ⟨2, by decide⟩),
   opAt 2887 .MUL,
   pushAt 2888 1 2,
   opAt 2889 .SUB,
   opAt 2890 .MUL,
   opAt 2891 (.Dup ⟨0, by decide⟩),
   opAt 2892 (.Dup ⟨2, by decide⟩),
   opAt 2893 .MUL,
   pushAt 2894 1 2,
   opAt 2895 .SUB,
   opAt 2896 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2897 .JUMPDEST,
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
   opAt 2909 .MUL,
   opAt 2910 (.Dup ⟨0, by decide⟩),
   opAt 2911 (.Dup ⟨2, by decide⟩),
   opAt 2912 .MUL,
   pushAt 2913 1 2,
   opAt 2914 .SUB,
   opAt 2915 .MUL,
   opAt 2916 (.Dup ⟨0, by decide⟩),
   opAt 2917 (.Dup ⟨2, by decide⟩),
   opAt 2918 .MUL,
   pushAt 2919 1 2,
   opAt 2920 .SUB,
   opAt 2921 .MUL,
   pushAt 2922 2 6272,
   opAt 2923 .MSTORE,
   opAt 2924 .POP,
   opAt 2925 .POP,
   opAt 2926 .POP,
   opAt 2927 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2928 .JUMPDEST,
   opAt 2929 (.Dup ⟨0, by decide⟩),
   opAt 2930 .ISZERO,
   pushAt 2931 2 4452,
   opAt 2932 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2933 (.Dup ⟨1, by decide⟩),
   pushAt 2934 2 2048,
   pushAt 2935 2 8224,
   opAt 2936 .MCOPY,
   pushAt 2937 0 0,
   pushAt 2938 2 9440,
   opAt 2939 .MLOAD,
   opAt 2940 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2941 .JUMPDEST,
   pushAt 2942 2 2048,
   opAt 2943 .MLOAD,
   pushAt 2944 2 6144,
   opAt 2945 .MLOAD,
   opAt 2946 (.Dup ⟨0, by decide⟩),
   opAt 2947 (.Dup ⟨2, by decide⟩),
   opAt 2948 .JUMPDEST,
   opAt 2949 .DIV,
   opAt 2950 (.Swap ⟨1, by decide⟩),
   opAt 2951 .MOD,
   pushAt 2952 2 6208,
   opAt 2953 .MLOAD,
   opAt 2954 .MUL,
   pushAt 2955 2 2080,
   opAt 2956 .MLOAD,
   pushAt 2957 2 6144,
   opAt 2958 .MLOAD,
   opAt 2959 (.Swap ⟨0, by decide⟩),
   opAt 2960 .DIV,
   opAt 2961 .ADD,
   pushAt 2962 2 6176,
   opAt 2963 .MLOAD,
   opAt 2964 (.Dup ⟨0, by decide⟩),
   pushAt 2965 2 6240,
   opAt 2966 .MLOAD,
   opAt 2967 (.Dup ⟨4, by decide⟩),
   opAt 2968 .MULMOD,
   opAt 2969 (.Dup ⟨2, by decide⟩),

   opAt 2970 .ADDMOD,
   opAt 2971 (.Swap ⟨0, by decide⟩),
   opAt 2972 .SUB,
   pushAt 2973 2 6272,
   opAt 2974 .MLOAD,
   opAt 2975 .MUL,
   opAt 2976 (.Dup ⟨0, by decide⟩),
   pushAt 2977 0 0,
   opAt 2978 .LT,
   opAt 2979 (.Swap ⟨0, by decide⟩),
   opAt 2980 .SUB,
   opAt 2981 (.Swap ⟨0, by decide⟩),
   pushAt 2982 2 6176,
   opAt 2983 .MLOAD,
   opAt 2984 .JUMPDEST,
   opAt 2985 .GT,
   opAt 2986 .ISZERO,
   pushAt 2987 0 0,
   opAt 2988 .SUB,
   opAt 2989 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2990 .JUMPDEST,
   pushAt 2991 0 0,
   pushAt 2992 2 9440,
   opAt 2993 .MLOAD,
   pushAt 2994 2 9408,
   opAt 2995 .MLOAD,
   pushAt 2996 2 5120,
   opAt 2997 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2998 .JUMPDEST,
   opAt 2999 (.Dup ⟨0, by decide⟩),
   opAt 3000 .MLOAD,
   pushAt 3001 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3002 (.Dup ⟨5, by decide⟩),
   opAt 3003 (.Dup ⟨2, by decide⟩),
   opAt 3004 .MUL,
   opAt 3005 (.Swap ⟨1, by decide⟩),
   opAt 3006 (.Dup ⟨6, by decide⟩),
   opAt 3007 .MULMOD,
   opAt 3008 (.Dup ⟨1, by decide⟩),
   opAt 3009 (.Dup ⟨1, by decide⟩),
   opAt 3010 .LT,
   opAt 3011 .SUB,
   opAt 3012 (.Dup ⟨4, by decide⟩),
   opAt 3013 (.Dup ⟨2, by decide⟩),
   opAt 3014 .ADD,
   opAt 3015 (.Dup ⟨0, by decide⟩),
   opAt 3016 (.Swap ⟨5, by decide⟩),
   opAt 3017 .GT,
   opAt 3018 .SUB,
   opAt 3019 .SUB,
   opAt 3020 (.Dup ⟨3, by decide⟩),
   opAt 3021 (.Dup ⟨3, by decide⟩),
   opAt 3022 .MLOAD,
   opAt 3023 .ADD,
   opAt 3024 (.Dup ⟨0, by decide⟩),
   opAt 3025 (.Swap ⟨4, by decide⟩),
   opAt 3026 .GT,
   opAt 3027 .ADD,
   opAt 3028 (.Swap ⟨2, by decide⟩),
   opAt 3029 (.Dup ⟨2, by decide⟩),
   pushAt 3030 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3031 .ADD,
   opAt 3032 (.Swap ⟨2, by decide⟩),
   opAt 3033 .MSTORE,
   pushAt 3034 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3035 .ADD,
   pushAt 3036 2 8224,
   opAt 3037 (.Dup ⟨2, by decide⟩),
   opAt 3038 .GT,
   pushAt 3039 2 4119,
   opAt 3040 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3041 .POP,
   opAt 3042 .POP,
   pushAt 3043 2 8224,
   opAt 3044 .MLOAD,
   opAt 3045 (.Dup ⟨1, by decide⟩),
   opAt 3046 .ADD,
   opAt 3047 (.Dup ⟨1, by decide⟩),
   opAt 3048 (.Dup ⟨1, by decide⟩),
   opAt 3049 .LT,
   opAt 3050 (.Swap ⟨1, by decide⟩),
   opAt 3051 .POP,
   opAt 3052 (.Dup ⟨2, by decide⟩),
   opAt 3053 (.Dup ⟨1, by decide⟩),
   opAt 3054 .LT,
   opAt 3055 (.Swap ⟨0, by decide⟩),
   opAt 3056 (.Dup ⟨3, by decide⟩),
   opAt 3057 (.Swap ⟨0, by decide⟩),
   opAt 3058 .SUB,
   opAt 3059 (.Dup ⟨0, by decide⟩),
   pushAt 3060 2 8224,
   opAt 3061 .MSTORE,
   opAt 3062 .POP,
   opAt 3063 .GT,
   opAt 3064 (.Swap ⟨0, by decide⟩),
   opAt 3065 .POP,
   opAt 3066 .ISZERO,
   pushAt 3067 2 4363,
   opAt 3068 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3069 .JUMPDEST,
   pushAt 3070 0 0,
   pushAt 3071 2 9440,
   opAt 3072 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3073 .JUMPDEST,
   opAt 3074 (.Dup ⟨0, by decide⟩),
   opAt 3075 .MLOAD,
   opAt 3076 (.Dup ⟨1, by decide⟩),
   pushAt 3077 2 8256,
   opAt 3078 (.Swap ⟨0, by decide⟩),
   opAt 3079 .SUB,
   opAt 3080 .MLOAD,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 .ADD,
   opAt 3083 (.Dup ⟨0, by decide⟩),
   opAt 3084 (.Dup ⟨2, by decide⟩),
   opAt 3085 .GT,
   opAt 3086 (.Swap ⟨1, by decide⟩),
   opAt 3087 .POP,
   opAt 3088 (.Dup ⟨3, by decide⟩),
   opAt 3089 .ADD,
   opAt 3090 (.Dup ⟨0, by decide⟩),
   opAt 3091 (.Dup ⟨4, by decide⟩),
   opAt 3092 .GT,
   opAt 3093 (.Swap ⟨3, by decide⟩),
   opAt 3094 .POP,
   opAt 3095 (.Dup ⟨2, by decide⟩),
   opAt 3096 .MSTORE,
   opAt 3097 (.Swap ⟨0, by decide⟩),
   opAt 3098 (.Swap ⟨1, by decide⟩),
   opAt 3099 .OR,
   opAt 3100 (.Swap ⟨0, by decide⟩),
   pushAt 3101 1 31, opAt 3102 .NOT,
   opAt 3103 .ADD,
   pushAt 3104 2 8255,
   opAt 3105 (.Dup ⟨1, by decide⟩),
   opAt 3106 .GT,
   pushAt 3107 2 4302,
   opAt 3108 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3109 .POP,
   pushAt 3110 2 8224,
   opAt 3111 .MLOAD,
   opAt 3112 (.Dup ⟨1, by decide⟩),
   opAt 3113 .ADD,
   opAt 3114 (.Dup ⟨0, by decide⟩),
   pushAt 3115 2 8224,
   opAt 3116 .MSTORE,
   opAt 3117 .LT,
   opAt 3118 .ISZERO,
   pushAt 3119 2 4296,
   opAt 3120 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3121 .JUMPDEST,
   pushAt 3122 2 8224,
   opAt 3123 .MLOAD,
   opAt 3124 .ISZERO,
   pushAt 3125 2 4432,
   opAt 3126 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3127 0 0,
   pushAt 3128 2 9440,
   opAt 3129 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3130 .JUMPDEST,
   opAt 3131 (.Dup ⟨0, by decide⟩),
   opAt 3132 .MLOAD,
   pushAt 3133 2 8256,
   opAt 3134 (.Dup ⟨2, by decide⟩),
   opAt 3135 .JUMPDEST,
   opAt 3136 .SUB,
   opAt 3137 .MLOAD,
   opAt 3138 (.Dup ⟨1, by decide⟩),
   opAt 3139 (.Dup ⟨1, by decide⟩),
   opAt 3140 .GT,
   opAt 3141 (.Swap ⟨1, by decide⟩),
   opAt 3142 .SUB,
   opAt 3143 (.Dup ⟨3, by decide⟩),
   opAt 3144 (.Dup ⟨1, by decide⟩),
   opAt 3145 .LT,
   opAt 3146 (.Swap ⟨0, by decide⟩),
   opAt 3147 (.Dup ⟨4, by decide⟩),
   opAt 3148 (.Swap ⟨0, by decide⟩),
   opAt 3149 .SUB,
   opAt 3150 (.Dup ⟨3, by decide⟩),
   opAt 3151 .MSTORE,
   opAt 3152 .OR,
   opAt 3153 (.Swap ⟨1, by decide⟩),
   opAt 3154 .POP,
   pushAt 3155 1 31, opAt 3156 .NOT,
   opAt 3157 .ADD,
   pushAt 3158 2 8255,
   opAt 3159 (.Dup ⟨1, by decide⟩),
   opAt 3160 .GT,
   pushAt 3161 2 4378,
   opAt 3162 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3163 .POP,
   pushAt 3164 2 8224,
   opAt 3165 .MLOAD,
   opAt 3166 .SUB,
   pushAt 3167 2 8224,
   opAt 3168 .MSTORE,
   pushAt 3169 2 4363,
   opAt 3170 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3171 .JUMPDEST,
   pushAt 3172 2 4443,
   pushAt 3173 2 2048,
   pushAt 3174 2 2304,
   opAt 3175 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3176 .JUMPDEST,
   pushAt 3177 1 1,
   opAt 3178 (.Swap ⟨0, by decide⟩),
   opAt 3179 .SUB,
   pushAt 3180 2 4017,
   opAt 3181 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3182 .JUMPDEST,
   opAt 3183 .POP,
   pushAt 3184 2 1756,
   opAt 3185 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3816 = true :=
  Artifact.isValidJumpDest_index 2776 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3860 = true :=
  Artifact.isValidJumpDest_index 2803 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2806 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3872 = true :=
  Artifact.isValidJumpDest_index 2810 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3903 = true :=
  Artifact.isValidJumpDest_index 2834 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3949 = true :=
  Artifact.isValidJumpDest_index 2871 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3980 = true :=
  Artifact.isValidJumpDest_index 2897 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4017 = true :=
  Artifact.isValidJumpDest_index 2928 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4038 = true :=
  Artifact.isValidJumpDest_index 2941 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4105 = true :=
  Artifact.isValidJumpDest_index 2990 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4119 = true :=
  Artifact.isValidJumpDest_index 2998 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4296 = true :=
  Artifact.isValidJumpDest_index 3069 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4302 = true :=
  Artifact.isValidJumpDest_index 3073 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4363 = true :=
  Artifact.isValidJumpDest_index 3121 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4378 = true :=
  Artifact.isValidJumpDest_index 3130 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4432 = true :=
  Artifact.isValidJumpDest_index 3171 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4443 = true :=
  Artifact.isValidJumpDest_index 3176 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4452 = true :=
  Artifact.isValidJumpDest_index 3182 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
