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
  [opAt 2768 .JUMPDEST,
   opAt 2769 (.Dup ⟨0, by decide⟩),
   opAt 2770 (.Dup ⟨3, by decide⟩),
   opAt 2771 .EQ,
   pushAt 2772 0 0,
   opAt 2773 .MLOAD,
   pushAt 2774 1 255,
   opAt 2775 .SHR,
   opAt 2776 .AND,
   opAt 2777 .ISZERO,
   pushAt 2778 2 3860,
   opAt 2779 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2780 (.Dup ⟨0, by decide⟩),
   pushAt 2781 1 96,
   pushAt 2782 2 1024,
   opAt 2783 .CALLDATACOPY,
   opAt 2784 (.Dup ⟨0, by decide⟩),
   pushAt 2785 1 96,
   pushAt 2786 2 8256,
   opAt 2787 .CALLDATACOPY,
   pushAt 2788 0 0,
   pushAt 2789 2 8224,
   opAt 2790 .MSTORE,
   pushAt 2791 2 3865,
   pushAt 2792 2 2048,
   pushAt 2793 2 2304,
   opAt 2794 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2795 .JUMPDEST,
   pushAt 2796 2 1533,
   opAt 2797 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2798 .JUMPDEST,
   pushAt 2799 1 1,
   pushAt 2800 2 9408,
   opAt 2801 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2802 .JUMPDEST,
   opAt 2803 (.Dup ⟨0, by decide⟩),
   opAt 2804 .MLOAD,
   opAt 2805 .NOT,
   opAt 2806 (.Dup ⟨2, by decide⟩),
   opAt 2807 .ADD,
   opAt 2808 (.Dup ⟨2, by decide⟩),
   opAt 2809 (.Dup ⟨1, by decide⟩),
   opAt 2810 .LT,
   opAt 2811 (.Swap ⟨2, by decide⟩),
   opAt 2812 .POP,
   opAt 2813 (.Dup ⟨1, by decide⟩),
   pushAt 2814 2 5120,
   opAt 2815 .ADD,
   opAt 2816 .MSTORE,
   opAt 2817 (.Dup ⟨0, by decide⟩),
   opAt 2818 .ISZERO,
   pushAt 2819 2 3903,
   opAt 2820 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2821 1 31, opAt 2822 .NOT,
   opAt 2823 .ADD,
   pushAt 2824 2 3872,
   opAt 2825 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2826 .JUMPDEST,
   opAt 2827 .POP,
   opAt 2828 .POP,
   pushAt 2829 0 0,
   opAt 2830 .MLOAD,
   opAt 2831 (.Dup ⟨0, by decide⟩),
   pushAt 2832 0 0,
   opAt 2833 .SUB,
   opAt 2834 (.Dup ⟨1, by decide⟩),
   opAt 2835 .AND,
   opAt 2836 (.Dup ⟨0, by decide⟩),
   pushAt 2837 2 6144,
   opAt 2838 .MSTORE,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 (.Dup ⟨2, by decide⟩),
   opAt 2841 .DIV,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   pushAt 2843 2 6176,
   opAt 2844 .MSTORE,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   pushAt 2846 0 0,
   opAt 2847 .SUB,
   opAt 2848 (.Dup ⟨2, by decide⟩),
   opAt 2849 (.Swap ⟨0, by decide⟩),
   opAt 2850 .DIV,
   pushAt 2851 1 1,
   opAt 2852 .ADD,
   pushAt 2853 2 6208,
   opAt 2854 .MSTORE,
   opAt 2855 (.Dup ⟨0, by decide⟩),
   pushAt 2856 0 0,
   opAt 2857 .SUB,
   opAt 2858 (.Dup ⟨1, by decide⟩),
   opAt 2859 (.Swap ⟨0, by decide⟩),
   opAt 2860 .MOD,
   pushAt 2861 2 6240,
   opAt 2862 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2863 (.Dup ⟨0, by decide⟩),
   pushAt 2864 1 3,
   opAt 2865 .MUL,
   pushAt 2866 1 2,
   opAt 2867 .XOR,
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
   opAt 2879 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2880 (.Dup ⟨0, by decide⟩),
   opAt 2881 (.Dup ⟨2, by decide⟩),
   opAt 2882 .MUL,
   pushAt 2883 1 2,
   opAt 2884 .SUB,
   opAt 2885 .MUL,
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
   pushAt 2904 2 6272,
   opAt 2905 .MSTORE,
   opAt 2906 .POP,
   opAt 2907 .POP,
   opAt 2908 .POP,
   pushAt 2909 1 32,
   opAt 2910 .MLOAD,
   pushAt 2911 1 128,
   opAt 2912 .SHR,
   pushAt 2913 2 6304,
   opAt 2914 .MSTORE,
   opAt 2915 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2916 .JUMPDEST,
   opAt 2917 (.Dup ⟨0, by decide⟩),
   opAt 2918 .ISZERO,
   pushAt 2919 2 4459,
   opAt 2920 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2921 (.Dup ⟨1, by decide⟩),
   pushAt 2922 2 2048,
   pushAt 2923 2 8224,
   opAt 2924 .MCOPY,
   pushAt 2925 0 0,
   pushAt 2926 2 9440,
   opAt 2927 .MLOAD,
   opAt 2928 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2929 2 2048,
   opAt 2930 .MLOAD,
   pushAt 2931 2 6144,
   opAt 2932 .MLOAD,
   opAt 2933 (.Dup ⟨1, by decide⟩),
   pushAt 2934 2 6208,
   opAt 2935 .MLOAD,
   opAt 2936 .MUL,
   opAt 2937 (.Dup ⟨1, by decide⟩),
   pushAt 2938 2 2080,
   opAt 2939 .MLOAD,
   opAt 2940 .DIV,
   opAt 2941 .ADD,
   opAt 2942 (.Swap ⟨1, by decide⟩),
   opAt 2943 .DIV,
   opAt 2944 (.Swap ⟨0, by decide⟩),
   pushAt 2945 2 6176,
   opAt 2946 .MLOAD,
   opAt 2947 (.Dup ⟨0, by decide⟩),
   pushAt 2948 2 6240,
   opAt 2949 .MLOAD,
   opAt 2950 (.Dup ⟨4, by decide⟩),
   opAt 2951 .MULMOD,
   opAt 2952 (.Dup ⟨2, by decide⟩),
   opAt 2953 .ADDMOD,
   opAt 2954 (.Swap ⟨0, by decide⟩),
   opAt 2955 .SUB,
   pushAt 2956 2 6272,
   opAt 2957 .MLOAD,
   opAt 2958 .MUL,
   opAt 2959 (.Dup ⟨0, by decide⟩),
   pushAt 2960 0 0,
   opAt 2961 .MLOAD,
   opAt 2962 .MUL,
   pushAt 2963 2 2080,
   opAt 2964 .MLOAD,
   opAt 2965 .SUB,
   pushAt 2966 2 6304,
   opAt 2967 .MLOAD,
   opAt 2968 (.Dup ⟨2, by decide⟩),
   pushAt 2969 1 128,
   opAt 2970 .SHR,
   opAt 2971 .MUL,
   opAt 2972 .GT,
   opAt 2973 (.Swap ⟨0, by decide⟩),
   opAt 2974 .SUB,
   opAt 2975 (.Swap ⟨0, by decide⟩),
   pushAt 2976 2 6176,
   opAt 2977 .MLOAD,
   opAt 2978 .GT,
   opAt 2979 .ISZERO,
   pushAt 2980 0 0,
   opAt 2981 .SUB,
   opAt 2982 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2983 .JUMPDEST,
   pushAt 2984 0 0,
   pushAt 2985 2 9440,
   opAt 2986 .MLOAD,
   pushAt 2987 2 9408,
   opAt 2988 .MLOAD,
   pushAt 2989 2 5120,
   opAt 2990 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2991 .JUMPDEST,
   opAt 2992 (.Dup ⟨0, by decide⟩),
   opAt 2993 .MLOAD,
   pushAt 2994 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2995 (.Dup ⟨5, by decide⟩),
   opAt 2996 (.Dup ⟨2, by decide⟩),
   opAt 2997 .MUL,
   opAt 2998 (.Swap ⟨1, by decide⟩),
   opAt 2999 (.Dup ⟨6, by decide⟩),
   opAt 3000 .MULMOD,
   opAt 3001 (.Dup ⟨1, by decide⟩),
   opAt 3002 (.Dup ⟨1, by decide⟩),
   opAt 3003 .LT,
   opAt 3004 .SUB,
   opAt 3005 (.Dup ⟨4, by decide⟩),
   opAt 3006 (.Dup ⟨2, by decide⟩),
   opAt 3007 .ADD,
   opAt 3008 (.Dup ⟨0, by decide⟩),
   opAt 3009 (.Swap ⟨5, by decide⟩),
   opAt 3010 .GT,
   opAt 3011 .SUB,
   opAt 3012 .SUB,
   opAt 3013 (.Dup ⟨3, by decide⟩),
   opAt 3014 (.Dup ⟨3, by decide⟩),
   opAt 3015 .MLOAD,
   opAt 3016 .ADD,
   opAt 3017 (.Dup ⟨0, by decide⟩),
   opAt 3018 (.Swap ⟨4, by decide⟩),
   opAt 3019 .GT,
   opAt 3020 .ADD,
   opAt 3021 (.Swap ⟨2, by decide⟩),
   opAt 3022 (.Dup ⟨2, by decide⟩),
   pushAt 3023 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3024 .ADD,
   opAt 3025 (.Swap ⟨2, by decide⟩),
   opAt 3026 .MSTORE,
   pushAt 3027 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3028 .ADD,
   pushAt 3029 2 8224,
   opAt 3030 (.Dup ⟨2, by decide⟩),
   opAt 3031 .GT,
   pushAt 3032 2 4126,
   opAt 3033 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3034 .POP,
   opAt 3035 .POP,
   pushAt 3036 2 8224,
   opAt 3037 .MLOAD,
   opAt 3038 (.Dup ⟨1, by decide⟩),
   opAt 3039 .ADD,
   opAt 3040 (.Dup ⟨1, by decide⟩),
   opAt 3041 (.Dup ⟨1, by decide⟩),
   opAt 3042 .LT,
   opAt 3043 (.Swap ⟨1, by decide⟩),
   opAt 3044 .POP,
   opAt 3045 (.Dup ⟨2, by decide⟩),
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 .LT,
   opAt 3048 (.Swap ⟨0, by decide⟩),
   opAt 3049 (.Dup ⟨3, by decide⟩),
   opAt 3050 (.Swap ⟨0, by decide⟩),
   opAt 3051 .SUB,
   opAt 3052 (.Dup ⟨0, by decide⟩),
   pushAt 3053 2 8224,
   opAt 3054 .MSTORE,
   opAt 3055 .POP,
   opAt 3056 .GT,
   opAt 3057 (.Swap ⟨0, by decide⟩),
   opAt 3058 .POP,
   opAt 3059 .ISZERO,
   pushAt 3060 2 4370,
   opAt 3061 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3062 .JUMPDEST,
   pushAt 3063 0 0,
   pushAt 3064 2 9440,
   opAt 3065 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3066 .JUMPDEST,
   opAt 3067 (.Dup ⟨0, by decide⟩),
   opAt 3068 .MLOAD,
   opAt 3069 (.Dup ⟨1, by decide⟩),
   pushAt 3070 2 8256,
   opAt 3071 (.Swap ⟨0, by decide⟩),
   opAt 3072 .SUB,
   opAt 3073 .MLOAD,
   opAt 3074 (.Dup ⟨1, by decide⟩),
   opAt 3075 .ADD,
   opAt 3076 (.Dup ⟨0, by decide⟩),
   opAt 3077 (.Dup ⟨2, by decide⟩),
   opAt 3078 .GT,
   opAt 3079 (.Swap ⟨1, by decide⟩),
   opAt 3080 .POP,
   opAt 3081 (.Dup ⟨3, by decide⟩),
   opAt 3082 .ADD,
   opAt 3083 (.Dup ⟨0, by decide⟩),
   opAt 3084 (.Dup ⟨4, by decide⟩),
   opAt 3085 .GT,
   opAt 3086 (.Swap ⟨3, by decide⟩),
   opAt 3087 .POP,
   opAt 3088 (.Dup ⟨2, by decide⟩),
   opAt 3089 .MSTORE,
   opAt 3090 (.Swap ⟨0, by decide⟩),
   opAt 3091 (.Swap ⟨1, by decide⟩),
   opAt 3092 .OR,
   opAt 3093 (.Swap ⟨0, by decide⟩),
   pushAt 3094 1 31, opAt 3095 .NOT,
   opAt 3096 .ADD,
   pushAt 3097 2 8255,
   opAt 3098 (.Dup ⟨1, by decide⟩),
   opAt 3099 .GT,
   pushAt 3100 2 4309,
   opAt 3101 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3102 .POP,
   pushAt 3103 2 8224,
   opAt 3104 .MLOAD,
   opAt 3105 (.Dup ⟨1, by decide⟩),
   opAt 3106 .ADD,
   opAt 3107 (.Dup ⟨0, by decide⟩),
   pushAt 3108 2 8224,
   opAt 3109 .MSTORE,
   opAt 3110 .LT,
   opAt 3111 .ISZERO,
   pushAt 3112 2 4303,
   opAt 3113 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3114 .JUMPDEST,
   pushAt 3115 2 8224,
   opAt 3116 .MLOAD,
   opAt 3117 .ISZERO,
   pushAt 3118 2 4439,
   opAt 3119 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3120 0 0,
   pushAt 3121 2 9440,
   opAt 3122 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3123 .JUMPDEST,
   opAt 3124 (.Dup ⟨0, by decide⟩),
   opAt 3125 .MLOAD,
   opAt 3126 (.Dup ⟨1, by decide⟩),
   pushAt 3127 2 8256,
   opAt 3128 (.Swap ⟨0, by decide⟩),
   opAt 3129 .SUB,
   opAt 3130 .MLOAD,
   opAt 3131 (.Dup ⟨1, by decide⟩),
   opAt 3132 (.Dup ⟨1, by decide⟩),
   opAt 3133 .GT,
   opAt 3134 (.Swap ⟨1, by decide⟩),
   opAt 3135 .SUB,
   opAt 3136 (.Dup ⟨3, by decide⟩),
   opAt 3137 (.Dup ⟨1, by decide⟩),
   opAt 3138 .LT,
   opAt 3139 (.Swap ⟨0, by decide⟩),
   opAt 3140 (.Dup ⟨4, by decide⟩),
   opAt 3141 (.Swap ⟨0, by decide⟩),
   opAt 3142 .SUB,
   opAt 3143 (.Dup ⟨3, by decide⟩),
   opAt 3144 .MSTORE,
   opAt 3145 .OR,
   opAt 3146 (.Swap ⟨1, by decide⟩),
   opAt 3147 .POP,
   pushAt 3148 1 31, opAt 3149 .NOT,
   opAt 3150 .ADD,
   pushAt 3151 2 8255,
   opAt 3152 (.Dup ⟨1, by decide⟩),
   opAt 3153 .GT,
   pushAt 3154 2 4385,
   opAt 3155 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3156 .POP,
   pushAt 3157 2 8224,
   opAt 3158 .MLOAD,
   opAt 3159 .SUB,
   pushAt 3160 2 8224,
   opAt 3161 .MSTORE,
   pushAt 3162 2 4370,
   opAt 3163 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3164 .JUMPDEST,
   pushAt 3165 2 4450,
   pushAt 3166 2 2048,
   pushAt 3167 2 2304,
   opAt 3168 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3169 .JUMPDEST,
   pushAt 3170 1 1,
   opAt 3171 (.Swap ⟨0, by decide⟩),
   opAt 3172 .SUB,
   pushAt 3173 2 4016,
   opAt 3174 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3175 .JUMPDEST,
   opAt 3176 .POP,
   pushAt 3177 2 1756,
   opAt 3178 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3816 = true :=
  Artifact.isValidJumpDest_index 2768 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3860 = true :=
  Artifact.isValidJumpDest_index 2795 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2798 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3872 = true :=
  Artifact.isValidJumpDest_index 2802 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3903 = true :=
  Artifact.isValidJumpDest_index 2826 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4016 = true :=
  Artifact.isValidJumpDest_index 2916 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4112 = true :=
  Artifact.isValidJumpDest_index 2983 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4126 = true :=
  Artifact.isValidJumpDest_index 2991 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4303 = true :=
  Artifact.isValidJumpDest_index 3062 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4309 = true :=
  Artifact.isValidJumpDest_index 3066 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4370 = true :=
  Artifact.isValidJumpDest_index 3114 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4385 = true :=
  Artifact.isValidJumpDest_index 3123 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4439 = true :=
  Artifact.isValidJumpDest_index 3164 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4450 = true :=
  Artifact.isValidJumpDest_index 3169 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4459 = true :=
  Artifact.isValidJumpDest_index 3175 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
