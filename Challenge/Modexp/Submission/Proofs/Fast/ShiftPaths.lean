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
  [opAt 2765 .JUMPDEST,
   opAt 2766 (.Dup ⟨0, by decide⟩),
   opAt 2767 (.Dup ⟨3, by decide⟩),
   opAt 2768 .EQ,
   pushAt 2769 0 0,
   opAt 2770 .MLOAD,
   pushAt 2771 1 255,
   opAt 2772 .SHR,
   opAt 2773 .AND,
   opAt 2774 .ISZERO,
   pushAt 2775 2 3824,
   opAt 2776 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2777 (.Dup ⟨0, by decide⟩),
   pushAt 2778 1 96,
   pushAt 2779 2 1024,
   opAt 2780 .CALLDATACOPY,
   opAt 2781 (.Dup ⟨0, by decide⟩),
   pushAt 2782 1 96,
   pushAt 2783 2 8256,
   opAt 2784 .CALLDATACOPY,
   pushAt 2785 0 0,
   pushAt 2786 2 8224,
   opAt 2787 .MSTORE,
   pushAt 2788 2 3829,
   pushAt 2789 2 2048,
   pushAt 2790 2 2288,
   opAt 2791 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2792 .JUMPDEST,
   pushAt 2793 2 1528,
   opAt 2794 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2795 .JUMPDEST,
   pushAt 2796 1 1,
   pushAt 2797 2 9408,
   opAt 2798 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2799 .JUMPDEST,
   opAt 2800 (.Dup ⟨0, by decide⟩),
   opAt 2801 .MLOAD,
   opAt 2802 .NOT,
   opAt 2803 (.Dup ⟨2, by decide⟩),
   opAt 2804 .ADD,
   opAt 2805 (.Dup ⟨2, by decide⟩),
   opAt 2806 (.Dup ⟨1, by decide⟩),
   opAt 2807 .LT,
   opAt 2808 (.Swap ⟨2, by decide⟩),
   opAt 2809 .POP,
   opAt 2810 (.Dup ⟨1, by decide⟩),
   pushAt 2811 2 5120,
   opAt 2812 .ADD,
   opAt 2813 .MSTORE,
   opAt 2814 (.Dup ⟨0, by decide⟩),
   opAt 2815 .ISZERO,
   pushAt 2816 2 3867,
   opAt 2817 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2818 1 31, opAt 2819 .NOT,
   opAt 2820 .ADD,
   pushAt 2821 2 3836,
   opAt 2822 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2823 .JUMPDEST,
   opAt 2824 .POP,
   opAt 2825 .POP,
   pushAt 2826 0 0,
   opAt 2827 .MLOAD,
   opAt 2828 (.Dup ⟨0, by decide⟩),
   pushAt 2829 0 0,
   opAt 2830 .SUB,
   opAt 2831 (.Dup ⟨1, by decide⟩),
   opAt 2832 .AND,
   opAt 2833 (.Dup ⟨0, by decide⟩),
   pushAt 2834 2 6144,
   opAt 2835 .MSTORE,
   opAt 2836 (.Dup ⟨0, by decide⟩),
   opAt 2837 (.Dup ⟨2, by decide⟩),
   opAt 2838 .DIV,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   pushAt 2840 2 6176,
   opAt 2841 .MSTORE,
   opAt 2842 (.Dup ⟨1, by decide⟩),
   pushAt 2843 0 0,
   opAt 2844 .SUB,
   opAt 2845 (.Dup ⟨2, by decide⟩),
   opAt 2846 (.Swap ⟨0, by decide⟩),
   opAt 2847 .DIV,
   pushAt 2848 1 1,
   opAt 2849 .ADD,
   pushAt 2850 2 6208,
   opAt 2851 .MSTORE,
   opAt 2852 (.Dup ⟨0, by decide⟩),
   pushAt 2853 0 0,
   opAt 2854 .SUB,
   opAt 2855 (.Dup ⟨1, by decide⟩),
   opAt 2856 (.Swap ⟨0, by decide⟩),
   opAt 2857 .MOD,
   pushAt 2858 2 6240,
   opAt 2859 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2860 (.Dup ⟨0, by decide⟩),
   pushAt 2861 1 2,
   opAt 2862 .SUB,
   opAt 2863 (.Dup ⟨0, by decide⟩),
   opAt 2864 (.Dup ⟨2, by decide⟩),
   opAt 2865 .MUL,
   pushAt 2866 1 2,
   opAt 2867 .SUB,
   opAt 2868 .MUL,
   opAt 2869 (.Dup ⟨0, by decide⟩),
   opAt 2870 (.Dup ⟨2, by decide⟩),
   opAt 2871 .MUL,
   pushAt 2872 1 2,
   opAt 2873 .SUB,
   opAt 2874 .MUL,
   opAt 2875 (.Dup ⟨0, by decide⟩),
   opAt 2876 (.Dup ⟨2, by decide⟩),
   opAt 2877 .MUL,
   pushAt 2878 1 2,
   opAt 2879 .SUB,
   opAt 2880 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2881 (.Dup ⟨0, by decide⟩),
   opAt 2882 (.Dup ⟨2, by decide⟩),
   opAt 2883 .MUL,
   pushAt 2884 1 2,
   opAt 2885 .SUB,
   opAt 2886 .MUL,
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
   pushAt 2905 2 6272,
   opAt 2906 .MSTORE,
   opAt 2907 .POP,
   opAt 2908 .POP,
   opAt 2909 .POP,
   opAt 2910 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2911 .JUMPDEST,
   opAt 2912 (.Dup ⟨0, by decide⟩),
   opAt 2913 .ISZERO,
   pushAt 2914 2 4418,
   opAt 2915 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2916 (.Dup ⟨1, by decide⟩),
   pushAt 2917 2 2048,
   pushAt 2918 2 8224,
   opAt 2919 .MCOPY,
   pushAt 2920 0 0,
   pushAt 2921 2 9440,
   opAt 2922 .MLOAD,
   opAt 2923 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2924 2 2048,
   opAt 2925 .MLOAD,
   pushAt 2926 2 6144,
   opAt 2927 .MLOAD,
   opAt 2928 (.Dup ⟨0, by decide⟩),
   opAt 2929 (.Dup ⟨2, by decide⟩),
   opAt 2930 .DIV,
   opAt 2931 (.Swap ⟨1, by decide⟩),
   opAt 2932 .MOD,
   pushAt 2933 2 6208,
   opAt 2934 .MLOAD,
   opAt 2935 .MUL,
   pushAt 2936 2 2080,
   opAt 2937 .MLOAD,
   pushAt 2938 2 6144,
   opAt 2939 .MLOAD,
   opAt 2940 (.Swap ⟨0, by decide⟩),
   opAt 2941 .DIV,
   opAt 2942 .ADD,
   pushAt 2943 2 6176,
   opAt 2944 .MLOAD,
   opAt 2945 (.Dup ⟨0, by decide⟩),
   pushAt 2946 2 6240,
   opAt 2947 .MLOAD,
   opAt 2948 (.Dup ⟨4, by decide⟩),
   opAt 2949 .MULMOD,
   opAt 2950 (.Dup ⟨2, by decide⟩),
   opAt 2951 .ADDMOD,
   opAt 2952 (.Swap ⟨0, by decide⟩),
   opAt 2953 .SUB,
   pushAt 2954 2 6272,
   opAt 2955 .MLOAD,
   opAt 2956 .MUL,
   opAt 2957 (.Dup ⟨0, by decide⟩),
   pushAt 2958 0 0,
   opAt 2959 .MLOAD,
   opAt 2960 .MUL,
   pushAt 2961 2 2080,
   opAt 2962 .MLOAD,
   opAt 2963 .SUB,
   pushAt 2964 1 32,
   opAt 2965 .MLOAD,
   opAt 2966 .GT,
   opAt 2967 (.Dup ⟨1, by decide⟩),
   pushAt 2968 0 0,
   opAt 2969 .LT,
   opAt 2970 .AND,
   opAt 2971 (.Swap ⟨0, by decide⟩),
   opAt 2972 .SUB,
   opAt 2973 (.Swap ⟨0, by decide⟩),
   pushAt 2974 2 6176,
   opAt 2975 .MLOAD,
   opAt 2976 .GT,
   opAt 2977 .ISZERO,
   pushAt 2978 0 0,
   opAt 2979 .SUB,
   opAt 2980 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2981 0 0,
   pushAt 2982 2 9440,
   opAt 2983 .MLOAD,
   pushAt 2984 2 9408,
   opAt 2985 .MLOAD,
   pushAt 2986 2 5120,
   opAt 2987 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2988 .JUMPDEST,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   opAt 2990 .MLOAD,
   pushAt 2991 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2992 (.Dup ⟨5, by decide⟩),
   opAt 2993 (.Dup ⟨2, by decide⟩),
   opAt 2994 .MUL,
   opAt 2995 (.Swap ⟨1, by decide⟩),
   opAt 2996 (.Dup ⟨6, by decide⟩),
   opAt 2997 .MULMOD,
   opAt 2998 (.Dup ⟨1, by decide⟩),
   opAt 2999 (.Dup ⟨1, by decide⟩),
   opAt 3000 .LT,
   opAt 3001 .SUB,
   opAt 3002 (.Dup ⟨4, by decide⟩),
   opAt 3003 (.Dup ⟨2, by decide⟩),
   opAt 3004 .ADD,
   opAt 3005 (.Dup ⟨0, by decide⟩),
   opAt 3006 (.Swap ⟨5, by decide⟩),
   opAt 3007 .GT,
   opAt 3008 .SUB,
   opAt 3009 .SUB,
   opAt 3010 (.Dup ⟨3, by decide⟩),
   opAt 3011 (.Dup ⟨3, by decide⟩),
   opAt 3012 .MLOAD,
   opAt 3013 .ADD,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   opAt 3015 (.Swap ⟨4, by decide⟩),
   opAt 3016 .GT,
   opAt 3017 .ADD,
   opAt 3018 (.Swap ⟨2, by decide⟩),
   opAt 3019 (.Dup ⟨2, by decide⟩),
   pushAt 3020 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3021 .ADD,
   opAt 3022 (.Swap ⟨2, by decide⟩),
   opAt 3023 .MSTORE,
   pushAt 3024 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3025 .ADD,
   pushAt 3026 2 8224,
   opAt 3027 (.Dup ⟨2, by decide⟩),
   opAt 3028 .GT,
   pushAt 3029 2 4086,
   opAt 3030 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3031 .POP,
   opAt 3032 .POP,
   pushAt 3033 2 8224,
   opAt 3034 .MLOAD,
   opAt 3035 (.Dup ⟨1, by decide⟩),
   opAt 3036 .ADD,
   opAt 3037 (.Dup ⟨1, by decide⟩),
   opAt 3038 (.Dup ⟨1, by decide⟩),
   opAt 3039 .LT,
   opAt 3040 (.Swap ⟨1, by decide⟩),
   opAt 3041 .POP,
   opAt 3042 (.Dup ⟨2, by decide⟩),
   opAt 3043 (.Dup ⟨1, by decide⟩),
   opAt 3044 .LT,
   opAt 3045 (.Swap ⟨0, by decide⟩),
   opAt 3046 (.Dup ⟨3, by decide⟩),
   opAt 3047 (.Swap ⟨0, by decide⟩),
   opAt 3048 .SUB,
   opAt 3049 (.Dup ⟨0, by decide⟩),
   pushAt 3050 2 8224,
   opAt 3051 .MSTORE,
   opAt 3052 .POP,
   opAt 3053 .GT,
   opAt 3054 (.Swap ⟨0, by decide⟩),
   opAt 3055 .POP,
   opAt 3056 .ISZERO,
   pushAt 3057 2 4330,
   opAt 3058 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3059 .JUMPDEST,
   pushAt 3060 0 0,
   pushAt 3061 2 9440,
   opAt 3062 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3063 .JUMPDEST,
   opAt 3064 (.Dup ⟨0, by decide⟩),
   opAt 3065 .MLOAD,
   opAt 3066 (.Dup ⟨1, by decide⟩),
   pushAt 3067 2 8256,
   opAt 3068 (.Swap ⟨0, by decide⟩),
   opAt 3069 .SUB,
   opAt 3070 .MLOAD,
   opAt 3071 (.Dup ⟨1, by decide⟩),
   opAt 3072 .ADD,
   opAt 3073 (.Dup ⟨0, by decide⟩),
   opAt 3074 (.Dup ⟨2, by decide⟩),
   opAt 3075 .GT,
   opAt 3076 (.Swap ⟨1, by decide⟩),
   opAt 3077 .POP,
   opAt 3078 (.Dup ⟨3, by decide⟩),
   opAt 3079 .ADD,
   opAt 3080 (.Dup ⟨0, by decide⟩),
   opAt 3081 (.Dup ⟨4, by decide⟩),
   opAt 3082 .GT,
   opAt 3083 (.Swap ⟨3, by decide⟩),
   opAt 3084 .POP,
   opAt 3085 (.Dup ⟨2, by decide⟩),
   opAt 3086 .MSTORE,
   opAt 3087 (.Swap ⟨0, by decide⟩),
   opAt 3088 (.Swap ⟨1, by decide⟩),
   opAt 3089 .OR,
   opAt 3090 (.Swap ⟨0, by decide⟩),
   pushAt 3091 1 31, opAt 3092 .NOT,
   opAt 3093 .ADD,
   pushAt 3094 2 8255,
   opAt 3095 (.Dup ⟨1, by decide⟩),
   opAt 3096 .GT,
   pushAt 3097 2 4269,
   opAt 3098 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3099 .POP,
   pushAt 3100 2 8224,
   opAt 3101 .MLOAD,
   opAt 3102 (.Dup ⟨1, by decide⟩),
   opAt 3103 .ADD,
   opAt 3104 (.Dup ⟨0, by decide⟩),
   pushAt 3105 2 8224,
   opAt 3106 .MSTORE,
   opAt 3107 .LT,
   opAt 3108 .ISZERO,
   pushAt 3109 2 4263,
   opAt 3110 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3111 .JUMPDEST,
   pushAt 3112 2 8224,
   opAt 3113 .MLOAD,
   opAt 3114 .ISZERO,
   pushAt 3115 2 4398,
   opAt 3116 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3117 0 0,
   pushAt 3118 2 9440,
   opAt 3119 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3120 .JUMPDEST,
   opAt 3121 (.Dup ⟨0, by decide⟩),
   opAt 3122 .MLOAD,
   pushAt 3123 2 8256,
   opAt 3124 (.Dup ⟨2, by decide⟩),
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
   pushAt 3150 2 4345,
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
   pushAt 3158 2 4330,
   opAt 3159 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3160 .JUMPDEST,
   pushAt 3161 2 4409,
   pushAt 3162 2 2048,
   pushAt 3163 2 2288,
   opAt 3164 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3165 .JUMPDEST,
   pushAt 3166 1 1,
   opAt 3167 (.Swap ⟨0, by decide⟩),
   opAt 3168 .SUB,
   pushAt 3169 2 3974,
   opAt 3170 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3171 .JUMPDEST,
   opAt 3172 .POP,
   pushAt 3173 2 1747,
   opAt 3174 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3780 = true :=
  Artifact.isValidJumpDest_index 2765 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3824 = true :=
  Artifact.isValidJumpDest_index 2792 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3829 = true :=
  Artifact.isValidJumpDest_index 2795 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3836 = true :=
  Artifact.isValidJumpDest_index 2799 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3867 = true :=
  Artifact.isValidJumpDest_index 2823 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3974 = true :=
  Artifact.isValidJumpDest_index 2911 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4086 = true :=
  Artifact.isValidJumpDest_index 2988 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4263 = true :=
  Artifact.isValidJumpDest_index 3059 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4269 = true :=
  Artifact.isValidJumpDest_index 3063 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4330 = true :=
  Artifact.isValidJumpDest_index 3111 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4345 = true :=
  Artifact.isValidJumpDest_index 3120 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4398 = true :=
  Artifact.isValidJumpDest_index 3160 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4409 = true :=
  Artifact.isValidJumpDest_index 3165 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4418 = true :=
  Artifact.isValidJumpDest_index 3171 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
