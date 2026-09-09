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
   pushAt 2786 2 3845,
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
   pushAt 2799 2 3850,
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
   pushAt 2827 2 3888,
   opAt 2828 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2829 1 31, opAt 2830 .NOT,
   opAt 2831 .ADD,
   pushAt 2832 2 3857,
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
   pushAt 2872 1 1,
   opAt 2873 (.Dup ⟨0, by decide⟩),
   opAt 2874 (.Dup ⟨2, by decide⟩),
   opAt 2875 .MUL,
   pushAt 2876 1 2,
   opAt 2877 .SUB,
   opAt 2878 .MUL,
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
  [pushAt 2941 2 2048,
   opAt 2942 .MLOAD,
   pushAt 2943 2 6144,
   opAt 2944 .MLOAD,
   opAt 2945 (.Dup ⟨0, by decide⟩),
   opAt 2946 (.Dup ⟨2, by decide⟩),
   opAt 2947 .DIV,
   opAt 2948 (.Swap ⟨1, by decide⟩),
   opAt 2949 .MOD,
   pushAt 2950 2 6208,
   opAt 2951 .MLOAD,
   opAt 2952 .MUL,
   pushAt 2953 2 2080,
   opAt 2954 .MLOAD,
   pushAt 2955 2 6144,
   opAt 2956 .MLOAD,
   opAt 2957 (.Swap ⟨0, by decide⟩),
   opAt 2958 .DIV,
   opAt 2959 .ADD,
   pushAt 2960 2 6176,
   opAt 2961 .MLOAD,
   opAt 2962 (.Dup ⟨0, by decide⟩),
   pushAt 2963 2 6240,
   opAt 2964 .MLOAD,
   opAt 2965 (.Dup ⟨4, by decide⟩),
   opAt 2966 .MULMOD,
   opAt 2967 (.Dup ⟨2, by decide⟩),
   opAt 2968 .ADDMOD,
   opAt 2969 (.Swap ⟨0, by decide⟩),
   opAt 2970 .SUB,
   pushAt 2971 2 6272,
   opAt 2972 .MLOAD,
   opAt 2973 .MUL,
   opAt 2974 (.Dup ⟨0, by decide⟩),
   pushAt 2975 0 0,
   opAt 2976 .MLOAD,
   opAt 2977 .MUL,
   pushAt 2978 2 2080,
   opAt 2979 .MLOAD,
   opAt 2980 .SUB,
   pushAt 2981 1 32,
   opAt 2982 .MLOAD,
   pushAt 2983 1 128,
   opAt 2984 .SHR,
   opAt 2985 (.Dup ⟨2, by decide⟩),
   pushAt 2986 1 128,
   opAt 2987 .SHR,
   opAt 2988 .MUL,
   opAt 2989 .GT,
   opAt 2990 (.Swap ⟨0, by decide⟩),
   opAt 2991 .SUB,
   opAt 2992 (.Swap ⟨0, by decide⟩),
   pushAt 2993 2 6176,
   opAt 2994 .MLOAD,
   opAt 2995 .GT,
   opAt 2996 .ISZERO,
   pushAt 2997 0 0,
   opAt 2998 .SUB,
   opAt 2999 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3000 .JUMPDEST,
   pushAt 3001 0 0,
   pushAt 3002 2 9440,
   opAt 3003 .MLOAD,
   pushAt 3004 2 9408,
   opAt 3005 .MLOAD,
   pushAt 3006 2 5120,
   opAt 3007 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3008 .JUMPDEST,
   opAt 3009 (.Dup ⟨0, by decide⟩),
   opAt 3010 .MLOAD,
   pushAt 3011 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3012 (.Dup ⟨5, by decide⟩),
   opAt 3013 (.Dup ⟨2, by decide⟩),
   opAt 3014 .MUL,
   opAt 3015 (.Swap ⟨1, by decide⟩),
   opAt 3016 (.Dup ⟨6, by decide⟩),
   opAt 3017 .MULMOD,
   opAt 3018 (.Dup ⟨1, by decide⟩),
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 .LT,
   opAt 3021 .SUB,
   opAt 3022 (.Dup ⟨4, by decide⟩),
   opAt 3023 (.Dup ⟨2, by decide⟩),
   opAt 3024 .ADD,
   opAt 3025 (.Dup ⟨0, by decide⟩),
   opAt 3026 (.Swap ⟨5, by decide⟩),
   opAt 3027 .GT,
   opAt 3028 .SUB,
   opAt 3029 .SUB,
   opAt 3030 (.Dup ⟨3, by decide⟩),
   opAt 3031 (.Dup ⟨3, by decide⟩),
   opAt 3032 .MLOAD,
   opAt 3033 .ADD,
   opAt 3034 (.Dup ⟨0, by decide⟩),
   opAt 3035 (.Swap ⟨4, by decide⟩),
   opAt 3036 .GT,
   opAt 3037 .ADD,
   opAt 3038 (.Swap ⟨2, by decide⟩),
   opAt 3039 (.Dup ⟨2, by decide⟩),
   pushAt 3040 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3041 .ADD,
   opAt 3042 (.Swap ⟨2, by decide⟩),
   opAt 3043 .MSTORE,
   pushAt 3044 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3045 .ADD,
   pushAt 3046 2 8224,
   opAt 3047 (.Dup ⟨2, by decide⟩),
   opAt 3048 .GT,
   pushAt 3049 2 4119,
   opAt 3050 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3051 .POP,
   opAt 3052 .POP,
   pushAt 3053 2 8224,
   opAt 3054 .MLOAD,
   opAt 3055 (.Dup ⟨1, by decide⟩),
   opAt 3056 .ADD,
   opAt 3057 (.Dup ⟨1, by decide⟩),
   opAt 3058 (.Dup ⟨1, by decide⟩),
   opAt 3059 .LT,
   opAt 3060 (.Swap ⟨1, by decide⟩),
   opAt 3061 .POP,
   opAt 3062 (.Dup ⟨2, by decide⟩),
   opAt 3063 (.Dup ⟨1, by decide⟩),
   opAt 3064 .LT,
   opAt 3065 (.Swap ⟨0, by decide⟩),
   opAt 3066 (.Dup ⟨3, by decide⟩),
   opAt 3067 (.Swap ⟨0, by decide⟩),
   opAt 3068 .SUB,
   opAt 3069 (.Dup ⟨0, by decide⟩),
   pushAt 3070 2 8224,
   opAt 3071 .MSTORE,
   opAt 3072 .POP,
   opAt 3073 .GT,
   opAt 3074 (.Swap ⟨0, by decide⟩),
   opAt 3075 .POP,
   opAt 3076 .ISZERO,
   pushAt 3077 2 4363,
   opAt 3078 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3079 .JUMPDEST,
   pushAt 3080 0 0,
   pushAt 3081 2 9440,
   opAt 3082 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3083 .JUMPDEST,
   opAt 3084 (.Dup ⟨0, by decide⟩),
   opAt 3085 .MLOAD,
   opAt 3086 (.Dup ⟨1, by decide⟩),
   pushAt 3087 2 8256,
   opAt 3088 (.Swap ⟨0, by decide⟩),
   opAt 3089 .SUB,
   opAt 3090 .MLOAD,
   opAt 3091 (.Dup ⟨1, by decide⟩),
   opAt 3092 .ADD,
   opAt 3093 (.Dup ⟨0, by decide⟩),
   opAt 3094 (.Dup ⟨2, by decide⟩),
   opAt 3095 .GT,
   opAt 3096 (.Swap ⟨1, by decide⟩),
   opAt 3097 .POP,
   opAt 3098 (.Dup ⟨3, by decide⟩),
   opAt 3099 .ADD,
   opAt 3100 (.Dup ⟨0, by decide⟩),
   opAt 3101 (.Dup ⟨4, by decide⟩),
   opAt 3102 .GT,
   opAt 3103 (.Swap ⟨3, by decide⟩),
   opAt 3104 .POP,
   opAt 3105 (.Dup ⟨2, by decide⟩),
   opAt 3106 .MSTORE,
   opAt 3107 (.Swap ⟨0, by decide⟩),
   opAt 3108 (.Swap ⟨1, by decide⟩),
   opAt 3109 .OR,
   opAt 3110 (.Swap ⟨0, by decide⟩),
   pushAt 3111 1 31, opAt 3112 .NOT,
   opAt 3113 .ADD,
   pushAt 3114 2 8255,
   opAt 3115 (.Dup ⟨1, by decide⟩),
   opAt 3116 .GT,
   pushAt 3117 2 4302,
   opAt 3118 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3119 .POP,
   pushAt 3120 2 8224,
   opAt 3121 .MLOAD,
   opAt 3122 (.Dup ⟨1, by decide⟩),
   opAt 3123 .ADD,
   opAt 3124 (.Dup ⟨0, by decide⟩),
   pushAt 3125 2 8224,
   opAt 3126 .MSTORE,
   opAt 3127 .LT,
   opAt 3128 .ISZERO,
   pushAt 3129 2 4296,
   opAt 3130 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3131 .JUMPDEST,
   pushAt 3132 2 8224,
   opAt 3133 .MLOAD,
   opAt 3134 .ISZERO,
   pushAt 3135 2 4432,
   opAt 3136 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3137 0 0,
   pushAt 3138 2 9440,
   opAt 3139 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3140 .JUMPDEST,
   opAt 3141 (.Dup ⟨0, by decide⟩),
   opAt 3142 .MLOAD,
   opAt 3143 (.Dup ⟨1, by decide⟩),
   pushAt 3144 2 8256,
   opAt 3145 (.Swap ⟨0, by decide⟩),
   opAt 3146 .SUB,
   opAt 3147 .MLOAD,
   opAt 3148 (.Dup ⟨1, by decide⟩),
   opAt 3149 (.Dup ⟨1, by decide⟩),
   opAt 3150 .GT,
   opAt 3151 (.Swap ⟨1, by decide⟩),
   opAt 3152 .SUB,
   opAt 3153 (.Dup ⟨3, by decide⟩),
   opAt 3154 (.Dup ⟨1, by decide⟩),
   opAt 3155 .LT,
   opAt 3156 (.Swap ⟨0, by decide⟩),
   opAt 3157 (.Dup ⟨4, by decide⟩),
   opAt 3158 (.Swap ⟨0, by decide⟩),
   opAt 3159 .SUB,
   opAt 3160 (.Dup ⟨3, by decide⟩),
   opAt 3161 .MSTORE,
   opAt 3162 .OR,
   opAt 3163 (.Swap ⟨1, by decide⟩),
   opAt 3164 .POP,
   pushAt 3165 1 31, opAt 3166 .NOT,
   opAt 3167 .ADD,
   pushAt 3168 2 8255,
   opAt 3169 (.Dup ⟨1, by decide⟩),
   opAt 3170 .GT,
   pushAt 3171 2 4378,
   opAt 3172 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3173 .POP,
   pushAt 3174 2 8224,
   opAt 3175 .MLOAD,
   opAt 3176 .SUB,
   pushAt 3177 2 8224,
   opAt 3178 .MSTORE,
   pushAt 3179 2 4363,
   opAt 3180 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3181 .JUMPDEST,
   pushAt 3182 2 4443,
   pushAt 3183 2 2048,
   pushAt 3184 2 2304,
   opAt 3185 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3186 .JUMPDEST,
   pushAt 3187 1 1,
   opAt 3188 (.Swap ⟨0, by decide⟩),
   opAt 3189 .SUB,
   pushAt 3190 2 4002,
   opAt 3191 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3192 .JUMPDEST,
   opAt 3193 .POP,
   pushAt 3194 2 1756,
   opAt 3195 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3801 = true :=
  Artifact.isValidJumpDest_index 2776 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3845 = true :=
  Artifact.isValidJumpDest_index 2803 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3850 = true :=
  Artifact.isValidJumpDest_index 2806 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3857 = true :=
  Artifact.isValidJumpDest_index 2810 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3888 = true :=
  Artifact.isValidJumpDest_index 2834 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3934 = true :=
  Artifact.isValidJumpDest_index 2871 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2897 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4002 = true :=
  Artifact.isValidJumpDest_index 2928 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4105 = true :=
  Artifact.isValidJumpDest_index 3000 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4119 = true :=
  Artifact.isValidJumpDest_index 3008 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4296 = true :=
  Artifact.isValidJumpDest_index 3079 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4302 = true :=
  Artifact.isValidJumpDest_index 3083 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4363 = true :=
  Artifact.isValidJumpDest_index 3131 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4378 = true :=
  Artifact.isValidJumpDest_index 3140 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4432 = true :=
  Artifact.isValidJumpDest_index 3181 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4443 = true :=
  Artifact.isValidJumpDest_index 3186 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4452 = true :=
  Artifact.isValidJumpDest_index 3192 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
