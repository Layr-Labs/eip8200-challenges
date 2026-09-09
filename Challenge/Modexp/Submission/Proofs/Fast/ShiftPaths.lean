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
  [opAt 2769 .JUMPDEST,
   opAt 2770 (.Dup ⟨0, by decide⟩),
   opAt 2771 (.Dup ⟨3, by decide⟩),
   opAt 2772 .EQ,
   pushAt 2773 0 0,
   opAt 2774 .MLOAD,
   pushAt 2775 1 255,
   opAt 2776 .SHR,
   opAt 2777 .AND,
   opAt 2778 .ISZERO,
   pushAt 2779 2 3860,
   opAt 2780 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2781 (.Dup ⟨0, by decide⟩),
   pushAt 2782 1 96,
   pushAt 2783 2 1024,
   opAt 2784 .CALLDATACOPY,
   opAt 2785 (.Dup ⟨0, by decide⟩),
   pushAt 2786 1 96,
   pushAt 2787 2 8256,
   opAt 2788 .CALLDATACOPY,
   pushAt 2789 0 0,
   pushAt 2790 2 8224,
   opAt 2791 .MSTORE,
   pushAt 2792 2 3865,
   pushAt 2793 2 2048,
   pushAt 2794 2 2304,
   opAt 2795 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2796 .JUMPDEST,
   pushAt 2797 2 1533,
   opAt 2798 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2799 .JUMPDEST,
   pushAt 2800 1 1,
   pushAt 2801 2 9408,
   opAt 2802 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2803 .JUMPDEST,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   opAt 2805 .MLOAD,
   opAt 2806 .NOT,
   opAt 2807 (.Dup ⟨2, by decide⟩),
   opAt 2808 .ADD,
   opAt 2809 (.Dup ⟨2, by decide⟩),
   opAt 2810 (.Dup ⟨1, by decide⟩),
   opAt 2811 .LT,
   opAt 2812 (.Swap ⟨2, by decide⟩),
   opAt 2813 .POP,
   opAt 2814 (.Dup ⟨1, by decide⟩),
   pushAt 2815 2 5120,
   opAt 2816 .ADD,
   opAt 2817 .MSTORE,
   opAt 2818 (.Dup ⟨0, by decide⟩),
   opAt 2819 .ISZERO,
   pushAt 2820 2 3903,
   opAt 2821 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2822 1 31, opAt 2823 .NOT,
   opAt 2824 .ADD,
   pushAt 2825 2 3872,
   opAt 2826 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2827 .JUMPDEST,
   opAt 2828 .POP,
   opAt 2829 .POP,
   pushAt 2830 0 0,
   opAt 2831 .MLOAD,
   opAt 2832 (.Dup ⟨0, by decide⟩),
   pushAt 2833 0 0,
   opAt 2834 .SUB,
   opAt 2835 (.Dup ⟨1, by decide⟩),
   opAt 2836 .AND,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   pushAt 2838 2 6144,
   opAt 2839 .MSTORE,
   opAt 2840 (.Dup ⟨0, by decide⟩),
   opAt 2841 (.Dup ⟨2, by decide⟩),
   opAt 2842 .DIV,
   opAt 2843 (.Dup ⟨0, by decide⟩),
   pushAt 2844 2 6176,
   opAt 2845 .MSTORE,
   opAt 2846 (.Dup ⟨1, by decide⟩),
   pushAt 2847 0 0,
   opAt 2848 .SUB,
   opAt 2849 (.Dup ⟨2, by decide⟩),
   opAt 2850 (.Swap ⟨0, by decide⟩),
   opAt 2851 .DIV,
   pushAt 2852 1 1,
   opAt 2853 .ADD,
   pushAt 2854 2 6208,
   opAt 2855 .MSTORE,
   opAt 2856 (.Dup ⟨0, by decide⟩),
   pushAt 2857 0 0,
   opAt 2858 .SUB,
   opAt 2859 (.Dup ⟨1, by decide⟩),
   opAt 2860 (.Swap ⟨0, by decide⟩),
   opAt 2861 .MOD,
   pushAt 2862 2 6240,
   opAt 2863 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2864 .JUMPDEST,
   opAt 2865 (.Dup ⟨0, by decide⟩),
   pushAt 2866 6 2,
   opAt 2867 .SUB,
   opAt 2868 (.Dup ⟨0, by decide⟩),
   opAt 2869 (.Dup ⟨2, by decide⟩),
   opAt 2870 .MUL,
   pushAt 2871 1 2,
   opAt 2872 .SUB,
   opAt 2873 .MUL,
   opAt 2874 (.Dup ⟨0, by decide⟩),
   opAt 2875 (.Dup ⟨2, by decide⟩),
   opAt 2876 .MUL,
   pushAt 2877 1 2,
   opAt 2878 .SUB,
   opAt 2879 .MUL,
   opAt 2880 (.Dup ⟨0, by decide⟩),
   opAt 2881 (.Dup ⟨2, by decide⟩),
   opAt 2882 .MUL,
   pushAt 2883 1 2,
   opAt 2884 .SUB,
   opAt 2885 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2886 .JUMPDEST,
   opAt 2887 (.Dup ⟨0, by decide⟩),
   opAt 2888 (.Dup ⟨2, by decide⟩),
   opAt 2889 .MUL,
   pushAt 2890 1 2,
   opAt 2891 .SUB,
   opAt 2892 .MUL,
   opAt 2893 (.Dup ⟨0, by decide⟩),
   opAt 2894 (.Dup ⟨2, by decide⟩),
   opAt 2895 .MUL,
   pushAt 2896 1 2,
   opAt 2897 .SUB,
   opAt 2898 .MUL,
   opAt 2899 (.Dup ⟨0, by decide⟩),
   opAt 2900 (.Dup ⟨2, by decide⟩),
   opAt 2901 .MUL,
   pushAt 2902 1 2,
   opAt 2903 .SUB,
   opAt 2904 .MUL,
   opAt 2905 (.Dup ⟨0, by decide⟩),
   opAt 2906 (.Dup ⟨2, by decide⟩),
   opAt 2907 .MUL,
   pushAt 2908 1 2,
   opAt 2909 .SUB,
   opAt 2910 .MUL,
   pushAt 2911 2 6272,
   opAt 2912 .MSTORE,
   opAt 2913 .POP,
   opAt 2914 .POP,
   opAt 2915 .POP,
   opAt 2916 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2917 .JUMPDEST,
   opAt 2918 (.Dup ⟨0, by decide⟩),
   opAt 2919 .ISZERO,
   pushAt 2920 2 4452,
   opAt 2921 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2922 (.Dup ⟨1, by decide⟩),
   pushAt 2923 2 2048,
   pushAt 2924 2 8224,
   opAt 2925 .MCOPY,
   pushAt 2926 0 0,
   pushAt 2927 2 9440,
   opAt 2928 .MLOAD,
   opAt 2929 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2930 .JUMPDEST,
   pushAt 2931 2 2048,
   opAt 2932 .MLOAD,
   pushAt 2933 2 6144,
   opAt 2934 .MLOAD,
   opAt 2935 (.Dup ⟨0, by decide⟩),
   opAt 2936 (.Dup ⟨2, by decide⟩),
   opAt 2937 .JUMPDEST,
   opAt 2938 .DIV,
   opAt 2939 (.Swap ⟨1, by decide⟩),
   opAt 2940 .MOD,
   pushAt 2941 2 6208,
   opAt 2942 .MLOAD,
   opAt 2943 .MUL,
   pushAt 2944 2 2080,
   opAt 2945 .MLOAD,
   pushAt 2946 2 6144,
   opAt 2947 .MLOAD,
   opAt 2948 (.Swap ⟨0, by decide⟩),
   opAt 2949 .DIV,
   opAt 2950 .ADD,
   pushAt 2951 2 6176,
   opAt 2952 .MLOAD,
   opAt 2953 (.Dup ⟨0, by decide⟩),
   pushAt 2954 2 6240,
   opAt 2955 .MLOAD,
   opAt 2956 (.Dup ⟨4, by decide⟩),
   opAt 2957 .MULMOD,
   opAt 2958 (.Dup ⟨2, by decide⟩),

   opAt 2959 .ADDMOD,
   opAt 2960 (.Swap ⟨0, by decide⟩),
   opAt 2961 .SUB,
   pushAt 2962 2 6272,
   opAt 2963 .MLOAD,
   opAt 2964 .MUL,
   opAt 2965 (.Dup ⟨0, by decide⟩),
   pushAt 2966 0 0,
   opAt 2967 .LT,
   opAt 2968 (.Swap ⟨0, by decide⟩),
   opAt 2969 .SUB,
   opAt 2970 (.Swap ⟨0, by decide⟩),
   pushAt 2971 2 6176,
   opAt 2972 .MLOAD,
   opAt 2973 .JUMPDEST,
   opAt 2974 .GT,
   opAt 2975 .ISZERO,
   pushAt 2976 0 0,
   opAt 2977 .SUB,
   opAt 2978 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2979 .JUMPDEST,
   pushAt 2980 0 0,
   pushAt 2981 2 9440,
   opAt 2982 .MLOAD,
   pushAt 2983 2 9408,
   opAt 2984 .MLOAD,
   pushAt 2985 2 5120,
   opAt 2986 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2987 .JUMPDEST,
   opAt 2988 (.Dup ⟨0, by decide⟩),
   opAt 2989 .MLOAD,
   pushAt 2990 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2991 (.Dup ⟨5, by decide⟩),
   opAt 2992 (.Dup ⟨2, by decide⟩),
   opAt 2993 .MUL,
   opAt 2994 (.Swap ⟨1, by decide⟩),
   opAt 2995 (.Dup ⟨6, by decide⟩),
   opAt 2996 .MULMOD,
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 (.Dup ⟨1, by decide⟩),
   opAt 2999 .LT,
   opAt 3000 .SUB,
   opAt 3001 (.Dup ⟨4, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   opAt 3003 .ADD,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 (.Swap ⟨5, by decide⟩),
   opAt 3006 .GT,
   opAt 3007 .SUB,
   opAt 3008 .SUB,
   opAt 3009 (.Dup ⟨3, by decide⟩),
   opAt 3010 (.Dup ⟨3, by decide⟩),
   opAt 3011 .MLOAD,
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Swap ⟨4, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 .ADD,
   opAt 3017 (.Swap ⟨2, by decide⟩),
   opAt 3018 (.Dup ⟨2, by decide⟩),
   pushAt 3019 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3020 .ADD,
   opAt 3021 (.Swap ⟨2, by decide⟩),
   opAt 3022 .MSTORE,
   pushAt 3023 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3024 .ADD,
   pushAt 3025 2 8224,
   opAt 3026 (.Dup ⟨2, by decide⟩),
   opAt 3027 .GT,
   pushAt 3028 2 4119,
   opAt 3029 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3030 .POP,
   opAt 3031 .POP,
   pushAt 3032 2 8224,
   opAt 3033 .MLOAD,
   opAt 3034 (.Dup ⟨1, by decide⟩),
   opAt 3035 .ADD,
   opAt 3036 (.Dup ⟨1, by decide⟩),
   opAt 3037 (.Dup ⟨1, by decide⟩),
   opAt 3038 .LT,
   opAt 3039 (.Swap ⟨1, by decide⟩),
   opAt 3040 .POP,
   opAt 3041 (.Dup ⟨2, by decide⟩),
   opAt 3042 (.Dup ⟨1, by decide⟩),
   opAt 3043 .LT,
   opAt 3044 (.Swap ⟨0, by decide⟩),
   opAt 3045 (.Dup ⟨3, by decide⟩),
   opAt 3046 (.Swap ⟨0, by decide⟩),
   opAt 3047 .SUB,
   opAt 3048 (.Dup ⟨0, by decide⟩),
   pushAt 3049 2 8224,
   opAt 3050 .MSTORE,
   opAt 3051 .POP,
   opAt 3052 .GT,
   opAt 3053 (.Swap ⟨0, by decide⟩),
   opAt 3054 .POP,
   opAt 3055 .ISZERO,
   pushAt 3056 2 4363,
   opAt 3057 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3058 .JUMPDEST,
   pushAt 3059 0 0,
   pushAt 3060 2 9440,
   opAt 3061 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3062 .JUMPDEST,
   opAt 3063 (.Dup ⟨0, by decide⟩),
   opAt 3064 .MLOAD,
   opAt 3065 (.Dup ⟨1, by decide⟩),
   pushAt 3066 2 8256,
   opAt 3067 (.Swap ⟨0, by decide⟩),
   opAt 3068 .SUB,
   opAt 3069 .MLOAD,
   opAt 3070 (.Dup ⟨1, by decide⟩),
   opAt 3071 .ADD,
   opAt 3072 (.Dup ⟨0, by decide⟩),
   opAt 3073 (.Dup ⟨2, by decide⟩),
   opAt 3074 .GT,
   opAt 3075 (.Swap ⟨1, by decide⟩),
   opAt 3076 .POP,
   opAt 3077 (.Dup ⟨3, by decide⟩),
   opAt 3078 .ADD,
   opAt 3079 (.Dup ⟨0, by decide⟩),
   opAt 3080 (.Dup ⟨4, by decide⟩),
   opAt 3081 .GT,
   opAt 3082 (.Swap ⟨3, by decide⟩),
   opAt 3083 .POP,
   opAt 3084 (.Dup ⟨2, by decide⟩),
   opAt 3085 .MSTORE,
   opAt 3086 (.Swap ⟨0, by decide⟩),
   opAt 3087 (.Swap ⟨1, by decide⟩),
   opAt 3088 .OR,
   opAt 3089 (.Swap ⟨0, by decide⟩),
   pushAt 3090 1 31, opAt 3091 .NOT,
   opAt 3092 .ADD,
   pushAt 3093 2 8255,
   opAt 3094 (.Dup ⟨1, by decide⟩),
   opAt 3095 .GT,
   pushAt 3096 2 4302,
   opAt 3097 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3098 .POP,
   pushAt 3099 2 8224,
   opAt 3100 .MLOAD,
   opAt 3101 (.Dup ⟨1, by decide⟩),
   opAt 3102 .ADD,
   opAt 3103 (.Dup ⟨0, by decide⟩),
   pushAt 3104 2 8224,
   opAt 3105 .MSTORE,
   opAt 3106 .LT,
   opAt 3107 .ISZERO,
   pushAt 3108 2 4296,
   opAt 3109 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 .JUMPDEST,
   pushAt 3111 2 8224,
   opAt 3112 .MLOAD,
   opAt 3113 .ISZERO,
   pushAt 3114 2 4432,
   opAt 3115 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3116 0 0,
   pushAt 3117 2 9440,
   opAt 3118 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3119 .JUMPDEST,
   opAt 3120 (.Dup ⟨0, by decide⟩),
   opAt 3121 .MLOAD,
   pushAt 3122 2 8256,
   opAt 3123 (.Dup ⟨2, by decide⟩),
   opAt 3124 .JUMPDEST,
   opAt 3125 .SUB,
   opAt 3126 .MLOAD,
   opAt 3127 (.Dup ⟨1, by decide⟩),
   opAt 3128 (.Dup ⟨1, by decide⟩),
   opAt 3129 .GT,
   opAt 3130 (.Swap ⟨1, by decide⟩),
   opAt 3131 .SUB,
   opAt 3132 (.Dup ⟨3, by decide⟩),
   opAt 3133 (.Dup ⟨1, by decide⟩),
   opAt 3134 .LT,
   opAt 3135 (.Swap ⟨0, by decide⟩),
   opAt 3136 (.Dup ⟨4, by decide⟩),
   opAt 3137 (.Swap ⟨0, by decide⟩),
   opAt 3138 .SUB,
   opAt 3139 (.Dup ⟨3, by decide⟩),
   opAt 3140 .MSTORE,
   opAt 3141 .OR,
   opAt 3142 (.Swap ⟨1, by decide⟩),
   opAt 3143 .POP,
   pushAt 3144 1 31, opAt 3145 .NOT,
   opAt 3146 .ADD,
   pushAt 3147 2 8255,
   opAt 3148 (.Dup ⟨1, by decide⟩),
   opAt 3149 .GT,
   pushAt 3150 2 4378,
   opAt 3151 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3152 .POP,
   pushAt 3153 2 8224,
   opAt 3154 .MLOAD,
   opAt 3155 .SUB,
   pushAt 3156 2 8224,
   opAt 3157 .MSTORE,
   pushAt 3158 2 4363,
   opAt 3159 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3160 .JUMPDEST,
   pushAt 3161 2 4443,
   pushAt 3162 2 2048,
   pushAt 3163 2 2304,
   opAt 3164 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3165 .JUMPDEST,
   pushAt 3166 1 1,
   opAt 3167 (.Swap ⟨0, by decide⟩),
   opAt 3168 .SUB,
   pushAt 3169 2 4017,
   opAt 3170 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3171 .JUMPDEST,
   opAt 3172 .POP,
   pushAt 3173 2 1756,
   opAt 3174 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3816 = true :=
  Artifact.isValidJumpDest_index 2769 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3860 = true :=
  Artifact.isValidJumpDest_index 2796 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2799 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3872 = true :=
  Artifact.isValidJumpDest_index 2803 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3903 = true :=
  Artifact.isValidJumpDest_index 2827 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3949 = true :=
  Artifact.isValidJumpDest_index 2864 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3980 = true :=
  Artifact.isValidJumpDest_index 2886 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4017 = true :=
  Artifact.isValidJumpDest_index 2917 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4038 = true :=
  Artifact.isValidJumpDest_index 2930 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4105 = true :=
  Artifact.isValidJumpDest_index 2979 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4119 = true :=
  Artifact.isValidJumpDest_index 2987 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4296 = true :=
  Artifact.isValidJumpDest_index 3058 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4302 = true :=
  Artifact.isValidJumpDest_index 3062 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4363 = true :=
  Artifact.isValidJumpDest_index 3110 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4378 = true :=
  Artifact.isValidJumpDest_index 3119 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4432 = true :=
  Artifact.isValidJumpDest_index 3160 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4443 = true :=
  Artifact.isValidJumpDest_index 3165 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4452 = true :=
  Artifact.isValidJumpDest_index 3171 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
