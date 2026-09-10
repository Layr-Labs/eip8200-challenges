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
  [opAt 2775 .JUMPDEST,
   opAt 2776 (.Dup ⟨0, by decide⟩),
   opAt 2777 (.Dup ⟨3, by decide⟩),
   opAt 2778 .EQ,
   pushAt 2779 0 0,
   opAt 2780 .MLOAD,
   pushAt 2781 1 255,
   opAt 2782 .SHR,
   opAt 2783 .AND,
   opAt 2784 .ISZERO,
   pushAt 2785 2 3843,
   opAt 2786 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2787 (.Dup ⟨0, by decide⟩),
   pushAt 2788 1 96,
   pushAt 2789 2 1024,
   opAt 2790 .CALLDATACOPY,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   pushAt 2792 1 96,
   pushAt 2793 2 8256,
   opAt 2794 .CALLDATACOPY,
   pushAt 2795 0 0,
   pushAt 2796 2 8224,
   opAt 2797 .MSTORE,
   pushAt 2798 2 3848,
   pushAt 2799 2 2048,
   pushAt 2800 2 2274,
   opAt 2801 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2802 .JUMPDEST,
   pushAt 2803 2 1526,
   opAt 2804 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2805 .JUMPDEST,
   pushAt 2806 1 1,
   pushAt 2807 2 9408,
   opAt 2808 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2809 .JUMPDEST,
   opAt 2810 (.Dup ⟨0, by decide⟩),
   opAt 2811 .MLOAD,
   opAt 2812 .NOT,
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 .ADD,
   opAt 2815 (.Dup ⟨2, by decide⟩),
   opAt 2816 (.Dup ⟨1, by decide⟩),
   opAt 2817 .LT,
   opAt 2818 (.Swap ⟨2, by decide⟩),
   opAt 2819 .POP,
   opAt 2820 (.Dup ⟨1, by decide⟩),
   pushAt 2821 2 5120,
   opAt 2822 .ADD,
   opAt 2823 .MSTORE,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   opAt 2825 .ISZERO,
   pushAt 2826 2 3886,
   opAt 2827 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2828 1 31, opAt 2829 .NOT,
   opAt 2830 .ADD,
   pushAt 2831 2 3855,
   opAt 2832 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2833 .JUMPDEST,
   opAt 2834 .POP,
   opAt 2835 .POP,
   pushAt 2836 0 0,
   opAt 2837 .MLOAD,
   opAt 2838 (.Dup ⟨0, by decide⟩),
   pushAt 2839 0 0,
   opAt 2840 .SUB,
   opAt 2841 (.Dup ⟨1, by decide⟩),
   opAt 2842 .AND,
   opAt 2843 (.Dup ⟨0, by decide⟩),
   pushAt 2844 2 6144,
   opAt 2845 .MSTORE,
   opAt 2846 (.Dup ⟨0, by decide⟩),
   opAt 2847 (.Dup ⟨2, by decide⟩),
   opAt 2848 .DIV,
   opAt 2849 (.Dup ⟨0, by decide⟩),
   pushAt 2850 2 6176,
   opAt 2851 .MSTORE,
   opAt 2852 (.Dup ⟨1, by decide⟩),
   pushAt 2853 0 0,
   opAt 2854 .SUB,
   opAt 2855 (.Dup ⟨2, by decide⟩),
   opAt 2856 (.Swap ⟨0, by decide⟩),
   opAt 2857 .DIV,
   pushAt 2858 1 1,
   opAt 2859 .ADD,
   pushAt 2860 2 6208,
   opAt 2861 .MSTORE,
   opAt 2862 (.Dup ⟨0, by decide⟩),
   pushAt 2863 0 0,
   opAt 2864 .SUB,
   opAt 2865 (.Dup ⟨1, by decide⟩),
   opAt 2866 (.Swap ⟨0, by decide⟩),
   opAt 2867 .MOD,
   pushAt 2868 2 6240,
   opAt 2869 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2870 .JUMPDEST,
   opAt 2871 (.Dup ⟨0, by decide⟩),
   pushAt 2872 1 2,
   opAt 2873 .SUB,
   opAt 2874 .JUMPDEST,
   opAt 2875 .JUMPDEST,
   opAt 2876 .JUMPDEST,
   opAt 2877 .JUMPDEST,
   opAt 2878 (.Dup ⟨0, by decide⟩),
   opAt 2879 (.Dup ⟨2, by decide⟩),
   opAt 2880 .MUL,
   pushAt 2881 1 2,
   opAt 2882 .SUB,
   opAt 2883 .MUL,
   opAt 2884 (.Dup ⟨0, by decide⟩),
   opAt 2885 (.Dup ⟨2, by decide⟩),
   opAt 2886 .MUL,
   pushAt 2887 1 2,
   opAt 2888 .SUB,
   opAt 2889 .MUL,
   opAt 2890 (.Dup ⟨0, by decide⟩),
   opAt 2891 (.Dup ⟨2, by decide⟩),
   opAt 2892 .MUL,
   pushAt 2893 1 2,
   opAt 2894 .SUB,
   opAt 2895 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2896 .JUMPDEST,
   opAt 2897 (.Dup ⟨0, by decide⟩),
   opAt 2898 (.Dup ⟨2, by decide⟩),
   opAt 2899 .MUL,
   pushAt 2900 1 2,
   opAt 2901 .SUB,
   opAt 2902 .MUL,
   opAt 2903 (.Dup ⟨0, by decide⟩),
   opAt 2904 (.Dup ⟨2, by decide⟩),
   opAt 2905 .MUL,
   pushAt 2906 1 2,
   opAt 2907 .SUB,
   opAt 2908 .MUL,
   opAt 2909 (.Dup ⟨0, by decide⟩),
   opAt 2910 (.Dup ⟨2, by decide⟩),
   opAt 2911 .MUL,
   pushAt 2912 1 2,
   opAt 2913 .SUB,
   opAt 2914 .MUL,
   opAt 2915 (.Dup ⟨0, by decide⟩),
   opAt 2916 (.Dup ⟨2, by decide⟩),
   opAt 2917 .MUL,
   pushAt 2918 1 2,
   opAt 2919 .SUB,
   opAt 2920 .MUL,
   pushAt 2921 2 6272,
   opAt 2922 .MSTORE,
   opAt 2923 .POP,
   opAt 2924 .POP,
   opAt 2925 .POP,
   opAt 2926 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2927 .JUMPDEST,
   opAt 2928 (.Dup ⟨0, by decide⟩),
   opAt 2929 .ISZERO,
   pushAt 2930 2 4434,
   opAt 2931 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2932 (.Dup ⟨1, by decide⟩),
   pushAt 2933 2 2048,
   pushAt 2934 2 8224,
   opAt 2935 .MCOPY,
   pushAt 2936 0 0,
   pushAt 2937 2 9440,
   opAt 2938 .MLOAD,
   opAt 2939 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2940 .JUMPDEST,
   pushAt 2941 2 2048,
   opAt 2942 .MLOAD,
   pushAt 2943 2 6144,
   opAt 2944 .MLOAD,
   opAt 2945 (.Dup ⟨1, by decide⟩),
   opAt 2946 (.Dup ⟨1, by decide⟩),
   opAt 2947 (.Swap ⟨0, by decide⟩),
   opAt 2948 .DIV,
   opAt 2949 (.Swap ⟨1, by decide⟩),
   opAt 2950 .MOD,
   pushAt 2951 2 6208,
   opAt 2952 .MLOAD,
   opAt 2953 .MUL,
   pushAt 2954 2 2080,
   opAt 2955 .MLOAD,
   pushAt 2956 2 6144,
   opAt 2957 .MLOAD,
   opAt 2958 (.Swap ⟨0, by decide⟩),
   opAt 2959 .DIV,
   opAt 2960 .ADD,
   pushAt 2961 2 6176,
   opAt 2962 .MLOAD,
   opAt 2963 (.Dup ⟨0, by decide⟩),
   pushAt 2964 2 6240,
   opAt 2965 .MLOAD,
   opAt 2966 (.Dup ⟨4, by decide⟩),
   opAt 2967 .MULMOD,
   opAt 2968 (.Dup ⟨2, by decide⟩),

   opAt 2969 .ADDMOD,
   opAt 2970 (.Swap ⟨0, by decide⟩),
   opAt 2971 .SUB,
   pushAt 2972 2 6272,
   opAt 2973 .MLOAD,
   opAt 2974 .MUL,
   opAt 2975 (.Dup ⟨0, by decide⟩),
   pushAt 2976 0 0,
   opAt 2977 .LT,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 .SUB,
   opAt 2980 (.Swap ⟨0, by decide⟩),
   pushAt 2981 2 6176,
   opAt 2982 .MLOAD,
   opAt 2983 .JUMPDEST,
   opAt 2984 .GT,
   opAt 2985 .ISZERO,
   pushAt 2986 0 0,
   opAt 2987 .SUB,
   opAt 2988 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2989 .JUMPDEST,
   pushAt 2990 0 0,
   pushAt 2991 2 9440,
   opAt 2992 .MLOAD,
   pushAt 2993 2 9408,
   opAt 2994 .MLOAD,
   pushAt 2995 2 5120,
   opAt 2996 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2997 .JUMPDEST,
   opAt 2998 (.Dup ⟨0, by decide⟩),
   opAt 2999 .MLOAD,
   pushAt 3000 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3001 (.Dup ⟨5, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   opAt 3003 .MUL,
   opAt 3004 (.Swap ⟨1, by decide⟩),
   opAt 3005 (.Dup ⟨6, by decide⟩),
   opAt 3006 .MULMOD,
   opAt 3007 (.Dup ⟨1, by decide⟩),
   opAt 3008 (.Dup ⟨1, by decide⟩),
   opAt 3009 .LT,
   opAt 3010 .SUB,
   opAt 3011 (.Dup ⟨4, by decide⟩),
   opAt 3012 (.Dup ⟨2, by decide⟩),
   opAt 3013 .ADD,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   opAt 3015 (.Swap ⟨5, by decide⟩),
   opAt 3016 .GT,
   opAt 3017 .SUB,
   opAt 3018 .SUB,
   opAt 3019 (.Dup ⟨3, by decide⟩),
   opAt 3020 (.Dup ⟨3, by decide⟩),
   opAt 3021 .MLOAD,
   opAt 3022 .ADD,
   opAt 3023 (.Dup ⟨0, by decide⟩),
   opAt 3024 (.Swap ⟨4, by decide⟩),
   opAt 3025 .GT,
   opAt 3026 .ADD,
   opAt 3027 (.Swap ⟨2, by decide⟩),
   opAt 3028 (.Dup ⟨2, by decide⟩),
   pushAt 3029 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3030 .ADD,
   opAt 3031 (.Swap ⟨2, by decide⟩),
   opAt 3032 .MSTORE,
   pushAt 3033 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3034 .ADD,
   pushAt 3035 2 8224,
   opAt 3036 (.Dup ⟨2, by decide⟩),
   opAt 3037 .GT,
   pushAt 3038 2 4101,
   opAt 3039 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3040 .POP,
   opAt 3041 .POP,
   pushAt 3042 2 8224,
   opAt 3043 .MLOAD,
   opAt 3044 (.Dup ⟨1, by decide⟩),
   opAt 3045 .ADD,
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 (.Dup ⟨1, by decide⟩),
   opAt 3048 .LT,
   opAt 3049 (.Swap ⟨1, by decide⟩),
   opAt 3050 .POP,
   opAt 3051 (.Dup ⟨2, by decide⟩),
   opAt 3052 (.Dup ⟨1, by decide⟩),
   opAt 3053 .LT,
   opAt 3054 (.Swap ⟨0, by decide⟩),
   opAt 3055 (.Dup ⟨3, by decide⟩),
   opAt 3056 (.Swap ⟨0, by decide⟩),
   opAt 3057 .SUB,
   opAt 3058 (.Dup ⟨0, by decide⟩),
   pushAt 3059 2 8224,
   opAt 3060 .MSTORE,
   opAt 3061 .POP,
   opAt 3062 .GT,
   opAt 3063 (.Swap ⟨0, by decide⟩),
   opAt 3064 .POP,
   opAt 3065 .ISZERO,
   pushAt 3066 2 4345,
   opAt 3067 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3068 .JUMPDEST,
   pushAt 3069 0 0,
   pushAt 3070 2 9440,
   opAt 3071 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3072 .JUMPDEST,
   opAt 3073 (.Dup ⟨0, by decide⟩),
   opAt 3074 .MLOAD,
   opAt 3075 (.Dup ⟨1, by decide⟩),
   pushAt 3076 2 8256,
   opAt 3077 (.Swap ⟨0, by decide⟩),
   opAt 3078 .SUB,
   opAt 3079 .MLOAD,
   opAt 3080 (.Dup ⟨1, by decide⟩),
   opAt 3081 .ADD,
   opAt 3082 (.Dup ⟨0, by decide⟩),
   opAt 3083 (.Dup ⟨2, by decide⟩),
   opAt 3084 .GT,
   opAt 3085 (.Swap ⟨1, by decide⟩),
   opAt 3086 .POP,
   opAt 3087 (.Dup ⟨3, by decide⟩),
   opAt 3088 .ADD,
   opAt 3089 (.Dup ⟨0, by decide⟩),
   opAt 3090 (.Dup ⟨4, by decide⟩),
   opAt 3091 .GT,
   opAt 3092 (.Swap ⟨3, by decide⟩),
   opAt 3093 .POP,
   opAt 3094 (.Dup ⟨2, by decide⟩),
   opAt 3095 .MSTORE,
   opAt 3096 (.Swap ⟨0, by decide⟩),
   opAt 3097 (.Swap ⟨1, by decide⟩),
   opAt 3098 .OR,
   opAt 3099 (.Swap ⟨0, by decide⟩),
   pushAt 3100 1 31, opAt 3101 .NOT,
   opAt 3102 .ADD,
   pushAt 3103 2 8255,
   opAt 3104 (.Dup ⟨1, by decide⟩),
   opAt 3105 .GT,
   pushAt 3106 2 4284,
   opAt 3107 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3108 .POP,
   pushAt 3109 2 8224,
   opAt 3110 .MLOAD,
   opAt 3111 (.Dup ⟨1, by decide⟩),
   opAt 3112 .ADD,
   opAt 3113 (.Dup ⟨0, by decide⟩),
   pushAt 3114 2 8224,
   opAt 3115 .MSTORE,
   opAt 3116 .LT,
   opAt 3117 .ISZERO,
   pushAt 3118 2 4278,
   opAt 3119 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3120 .JUMPDEST,
   pushAt 3121 2 8224,
   opAt 3122 .MLOAD,
   opAt 3123 .ISZERO,
   pushAt 3124 2 4414,
   opAt 3125 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3126 0 0,
   pushAt 3127 2 9440,
   opAt 3128 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3129 .JUMPDEST,
   opAt 3130 (.Dup ⟨0, by decide⟩),
   opAt 3131 .MLOAD,
   opAt 3132 (.Dup ⟨1, by decide⟩),
   pushAt 3133 2 8256,
   opAt 3134 (.Swap ⟨0, by decide⟩),
   opAt 3135 .SUB,
   opAt 3136 .MLOAD,
   opAt 3137 (.Dup ⟨1, by decide⟩),
   opAt 3138 (.Dup ⟨1, by decide⟩),
   opAt 3139 .GT,
   opAt 3140 (.Swap ⟨1, by decide⟩),
   opAt 3141 .SUB,
   opAt 3142 (.Dup ⟨3, by decide⟩),
   opAt 3143 (.Dup ⟨1, by decide⟩),
   opAt 3144 .LT,
   opAt 3145 (.Swap ⟨0, by decide⟩),
   opAt 3146 (.Dup ⟨4, by decide⟩),
   opAt 3147 (.Swap ⟨0, by decide⟩),
   opAt 3148 .SUB,
   opAt 3149 (.Dup ⟨3, by decide⟩),
   opAt 3150 .MSTORE,
   opAt 3151 .OR,
   opAt 3152 (.Swap ⟨1, by decide⟩),
   opAt 3153 .POP,
   pushAt 3154 1 31, opAt 3155 .NOT,
   opAt 3156 .ADD,
   pushAt 3157 2 8255,
   opAt 3158 (.Dup ⟨1, by decide⟩),
   opAt 3159 .GT,
   pushAt 3160 2 4360,
   opAt 3161 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3162 .POP,
   pushAt 3163 2 8224,
   opAt 3164 .MLOAD,
   opAt 3165 .SUB,
   pushAt 3166 2 8224,
   opAt 3167 .MSTORE,
   pushAt 3168 2 4345,
   opAt 3169 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3170 .JUMPDEST,
   pushAt 3171 2 4425,
   pushAt 3172 2 2048,
   pushAt 3173 2 2274,
   opAt 3174 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3175 .JUMPDEST,
   pushAt 3176 1 1,
   opAt 3177 (.Swap ⟨0, by decide⟩),
   opAt 3178 .SUB,
   pushAt 3179 2 3999,
   opAt 3180 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3181 .JUMPDEST,
   opAt 3182 .POP,
   pushAt 3183 2 1737,
   opAt 3184 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3799 = true :=
  Artifact.isValidJumpDest_index 2775 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3843 = true :=
  Artifact.isValidJumpDest_index 2802 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3848 = true :=
  Artifact.isValidJumpDest_index 2805 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3855 = true :=
  Artifact.isValidJumpDest_index 2809 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3886 = true :=
  Artifact.isValidJumpDest_index 2833 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3932 = true :=
  Artifact.isValidJumpDest_index 2870 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3962 = true :=
  Artifact.isValidJumpDest_index 2896 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3999 = true :=
  Artifact.isValidJumpDest_index 2927 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4020 = true :=
  Artifact.isValidJumpDest_index 2940 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4087 = true :=
  Artifact.isValidJumpDest_index 2989 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4101 = true :=
  Artifact.isValidJumpDest_index 2997 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4278 = true :=
  Artifact.isValidJumpDest_index 3068 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4284 = true :=
  Artifact.isValidJumpDest_index 3072 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4345 = true :=
  Artifact.isValidJumpDest_index 3120 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4360 = true :=
  Artifact.isValidJumpDest_index 3129 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4414 = true :=
  Artifact.isValidJumpDest_index 3170 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4425 = true :=
  Artifact.isValidJumpDest_index 3175 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4434 = true :=
  Artifact.isValidJumpDest_index 3181 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
