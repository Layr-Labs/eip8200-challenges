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
  [opAt 2767 .JUMPDEST,
   opAt 2768 (.Dup ⟨0, by decide⟩),
   opAt 2769 (.Dup ⟨3, by decide⟩),
   opAt 2770 .EQ,
   pushAt 2771 0 0,
   opAt 2772 .MLOAD,
   pushAt 2773 1 255,
   opAt 2774 .SHR,
   opAt 2775 .AND,
   opAt 2776 .ISZERO,
   pushAt 2777 2 3824,
   opAt 2778 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2779 (.Dup ⟨0, by decide⟩),
   pushAt 2780 1 96,
   pushAt 2781 2 1024,
   opAt 2782 .CALLDATACOPY,
   opAt 2783 (.Dup ⟨0, by decide⟩),
   pushAt 2784 1 96,
   pushAt 2785 2 8256,
   opAt 2786 .CALLDATACOPY,
   pushAt 2787 0 0,
   pushAt 2788 2 8224,
   opAt 2789 .MSTORE,
   pushAt 2790 2 3829,
   pushAt 2791 2 2048,
   pushAt 2792 2 2288,
   opAt 2793 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2794 .JUMPDEST,
   pushAt 2795 2 1528,
   opAt 2796 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2797 .JUMPDEST,
   pushAt 2798 1 1,
   pushAt 2799 2 9408,
   opAt 2800 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2801 .JUMPDEST,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   opAt 2803 .MLOAD,
   opAt 2804 .NOT,
   opAt 2805 (.Dup ⟨2, by decide⟩),
   opAt 2806 .ADD,
   opAt 2807 (.Dup ⟨2, by decide⟩),
   opAt 2808 (.Dup ⟨1, by decide⟩),
   opAt 2809 .LT,
   opAt 2810 (.Swap ⟨2, by decide⟩),
   opAt 2811 .POP,
   opAt 2812 (.Dup ⟨1, by decide⟩),
   pushAt 2813 2 5120,
   opAt 2814 .ADD,
   opAt 2815 .MSTORE,
   opAt 2816 (.Dup ⟨0, by decide⟩),
   opAt 2817 .ISZERO,
   pushAt 2818 2 3867,
   opAt 2819 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2820 1 31, opAt 2821 .NOT,
   opAt 2822 .ADD,
   pushAt 2823 2 3836,
   opAt 2824 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2825 .JUMPDEST,
   opAt 2826 .POP,
   opAt 2827 .POP,
   pushAt 2828 0 0,
   opAt 2829 .MLOAD,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   pushAt 2831 0 0,
   opAt 2832 .SUB,
   opAt 2833 (.Dup ⟨1, by decide⟩),
   opAt 2834 .AND,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   pushAt 2836 2 6144,
   opAt 2837 .MSTORE,
   opAt 2838 (.Dup ⟨0, by decide⟩),
   opAt 2839 (.Dup ⟨2, by decide⟩),
   opAt 2840 .DIV,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   pushAt 2842 2 6176,
   opAt 2843 .MSTORE,
   opAt 2844 (.Dup ⟨1, by decide⟩),
   pushAt 2845 0 0,
   opAt 2846 .SUB,
   opAt 2847 (.Dup ⟨2, by decide⟩),
   opAt 2848 (.Swap ⟨0, by decide⟩),
   opAt 2849 .DIV,
   pushAt 2850 1 1,
   opAt 2851 .ADD,
   pushAt 2852 2 6208,
   opAt 2853 .MSTORE,
   opAt 2854 (.Dup ⟨0, by decide⟩),
   pushAt 2855 0 0,
   opAt 2856 .SUB,
   opAt 2857 (.Dup ⟨1, by decide⟩),
   opAt 2858 (.Swap ⟨0, by decide⟩),
   opAt 2859 .MOD,
   pushAt 2860 2 6240,
   opAt 2861 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2862 (.Dup ⟨0, by decide⟩),
   pushAt 2863 1 2,
   opAt 2864 .SUB,
   opAt 2865 (.Dup ⟨0, by decide⟩),
   opAt 2866 (.Dup ⟨2, by decide⟩),
   opAt 2867 .MUL,
   pushAt 2868 1 2,
   opAt 2869 .SUB,
   opAt 2870 .MUL,
   opAt 2871 (.Dup ⟨0, by decide⟩),
   opAt 2872 (.Dup ⟨2, by decide⟩),
   opAt 2873 .MUL,
   pushAt 2874 1 2,
   opAt 2875 .SUB,
   opAt 2876 .MUL,
   opAt 2877 (.Dup ⟨0, by decide⟩),
   opAt 2878 (.Dup ⟨2, by decide⟩),
   opAt 2879 .MUL,
   pushAt 2880 1 2,
   opAt 2881 .SUB,
   opAt 2882 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2883 (.Dup ⟨0, by decide⟩),
   opAt 2884 (.Dup ⟨2, by decide⟩),
   opAt 2885 .MUL,
   pushAt 2886 1 2,
   opAt 2887 .SUB,
   opAt 2888 .MUL,
   opAt 2889 (.Dup ⟨0, by decide⟩),
   opAt 2890 (.Dup ⟨2, by decide⟩),
   opAt 2891 .MUL,
   pushAt 2892 1 2,
   opAt 2893 .SUB,
   opAt 2894 .MUL,
   opAt 2895 (.Dup ⟨0, by decide⟩),
   opAt 2896 (.Dup ⟨2, by decide⟩),
   opAt 2897 .MUL,
   pushAt 2898 1 2,
   opAt 2899 .SUB,
   opAt 2900 .MUL,
   opAt 2901 (.Dup ⟨0, by decide⟩),
   opAt 2902 (.Dup ⟨2, by decide⟩),
   opAt 2903 .MUL,
   pushAt 2904 1 2,
   opAt 2905 .SUB,
   opAt 2906 .MUL,
   pushAt 2907 2 6272,
   opAt 2908 .MSTORE,
   opAt 2909 .POP,
   opAt 2910 .POP,
   opAt 2911 .POP,
   opAt 2912 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2913 .JUMPDEST,
   opAt 2914 (.Dup ⟨0, by decide⟩),
   opAt 2915 .ISZERO,
   pushAt 2916 2 4422,
   opAt 2917 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2918 (.Dup ⟨1, by decide⟩),
   pushAt 2919 2 2048,
   pushAt 2920 2 8224,
   opAt 2921 .MCOPY,
   pushAt 2922 0 0,
   pushAt 2923 2 9440,
   opAt 2924 .MLOAD,
   opAt 2925 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2926 2 2048,
   opAt 2927 .MLOAD,
   pushAt 2928 2 6144,
   opAt 2929 .MLOAD,
   opAt 2930 (.Dup ⟨0, by decide⟩),
   opAt 2931 (.Dup ⟨2, by decide⟩),
   opAt 2932 .DIV,
   opAt 2933 (.Swap ⟨1, by decide⟩),
   opAt 2934 .MOD,
   pushAt 2935 2 6208,
   opAt 2936 .MLOAD,
   opAt 2937 .MUL,
   pushAt 2938 2 2080,
   opAt 2939 .MLOAD,
   pushAt 2940 2 6144,
   opAt 2941 .MLOAD,
   opAt 2942 (.Swap ⟨0, by decide⟩),
   opAt 2943 .DIV,
   opAt 2944 .ADD,
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
   pushAt 2966 1 32,
   opAt 2967 .MLOAD,
   pushAt 2968 1 128,
   opAt 2969 .SHR,
   opAt 2970 (.Dup ⟨2, by decide⟩),
   pushAt 2971 1 128,
   opAt 2972 .SHR,
   opAt 2973 .MUL,
   opAt 2974 .GT,
   opAt 2975 (.Swap ⟨0, by decide⟩),
   opAt 2976 .SUB,
   opAt 2977 (.Swap ⟨0, by decide⟩),
   pushAt 2978 2 6176,
   opAt 2979 .MLOAD,
   opAt 2980 .GT,
   opAt 2981 .ISZERO,
   pushAt 2982 0 0,
   opAt 2983 .SUB,
   opAt 2984 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2985 0 0,
   pushAt 2986 2 9440,
   opAt 2987 .MLOAD,
   pushAt 2988 2 9408,
   opAt 2989 .MLOAD,
   pushAt 2990 2 5120,
   opAt 2991 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2992 .JUMPDEST,
   opAt 2993 (.Dup ⟨0, by decide⟩),
   opAt 2994 .MLOAD,
   pushAt 2995 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2996 (.Dup ⟨5, by decide⟩),
   opAt 2997 (.Dup ⟨2, by decide⟩),
   opAt 2998 .MUL,
   opAt 2999 (.Swap ⟨1, by decide⟩),
   opAt 3000 (.Dup ⟨6, by decide⟩),
   opAt 3001 .MULMOD,
   opAt 3002 (.Dup ⟨1, by decide⟩),
   opAt 3003 (.Dup ⟨1, by decide⟩),
   opAt 3004 .LT,
   opAt 3005 .SUB,
   opAt 3006 (.Dup ⟨4, by decide⟩),
   opAt 3007 (.Dup ⟨2, by decide⟩),
   opAt 3008 .ADD,
   opAt 3009 (.Dup ⟨0, by decide⟩),
   opAt 3010 (.Swap ⟨5, by decide⟩),
   opAt 3011 .GT,
   opAt 3012 .SUB,
   opAt 3013 .SUB,
   opAt 3014 (.Dup ⟨3, by decide⟩),
   opAt 3015 (.Dup ⟨3, by decide⟩),
   opAt 3016 .MLOAD,
   opAt 3017 .ADD,
   opAt 3018 (.Dup ⟨0, by decide⟩),
   opAt 3019 (.Swap ⟨4, by decide⟩),
   opAt 3020 .GT,
   opAt 3021 .ADD,
   opAt 3022 (.Swap ⟨2, by decide⟩),
   opAt 3023 (.Dup ⟨2, by decide⟩),
   pushAt 3024 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3025 .ADD,
   opAt 3026 (.Swap ⟨2, by decide⟩),
   opAt 3027 .MSTORE,
   pushAt 3028 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3029 .ADD,
   pushAt 3030 2 8224,
   opAt 3031 (.Dup ⟨2, by decide⟩),
   opAt 3032 .GT,
   pushAt 3033 2 4090,
   opAt 3034 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3035 .POP,
   opAt 3036 .POP,
   pushAt 3037 2 8224,
   opAt 3038 .MLOAD,
   opAt 3039 (.Dup ⟨1, by decide⟩),
   opAt 3040 .ADD,
   opAt 3041 (.Dup ⟨1, by decide⟩),
   opAt 3042 (.Dup ⟨1, by decide⟩),
   opAt 3043 .LT,
   opAt 3044 (.Swap ⟨1, by decide⟩),
   opAt 3045 .POP,
   opAt 3046 (.Dup ⟨2, by decide⟩),
   opAt 3047 (.Dup ⟨1, by decide⟩),
   opAt 3048 .LT,
   opAt 3049 (.Swap ⟨0, by decide⟩),
   opAt 3050 (.Dup ⟨3, by decide⟩),
   opAt 3051 (.Swap ⟨0, by decide⟩),
   opAt 3052 .SUB,
   opAt 3053 (.Dup ⟨0, by decide⟩),
   pushAt 3054 2 8224,
   opAt 3055 .MSTORE,
   opAt 3056 .POP,
   opAt 3057 .GT,
   opAt 3058 (.Swap ⟨0, by decide⟩),
   opAt 3059 .POP,
   opAt 3060 .ISZERO,
   pushAt 3061 2 4334,
   opAt 3062 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3063 .JUMPDEST,
   pushAt 3064 0 0,
   pushAt 3065 2 9440,
   opAt 3066 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3067 .JUMPDEST,
   opAt 3068 (.Dup ⟨0, by decide⟩),
   opAt 3069 .MLOAD,
   opAt 3070 (.Dup ⟨1, by decide⟩),
   pushAt 3071 2 8256,
   opAt 3072 (.Swap ⟨0, by decide⟩),
   opAt 3073 .SUB,
   opAt 3074 .MLOAD,
   opAt 3075 (.Dup ⟨1, by decide⟩),
   opAt 3076 .ADD,
   opAt 3077 (.Dup ⟨0, by decide⟩),
   opAt 3078 (.Dup ⟨2, by decide⟩),
   opAt 3079 .GT,
   opAt 3080 (.Swap ⟨1, by decide⟩),
   opAt 3081 .POP,
   opAt 3082 (.Dup ⟨3, by decide⟩),
   opAt 3083 .ADD,
   opAt 3084 (.Dup ⟨0, by decide⟩),
   opAt 3085 (.Dup ⟨4, by decide⟩),
   opAt 3086 .GT,
   opAt 3087 (.Swap ⟨3, by decide⟩),
   opAt 3088 .POP,
   opAt 3089 (.Dup ⟨2, by decide⟩),
   opAt 3090 .MSTORE,
   opAt 3091 (.Swap ⟨0, by decide⟩),
   opAt 3092 (.Swap ⟨1, by decide⟩),
   opAt 3093 .OR,
   opAt 3094 (.Swap ⟨0, by decide⟩),
   pushAt 3095 1 31, opAt 3096 .NOT,
   opAt 3097 .ADD,
   pushAt 3098 2 8255,
   opAt 3099 (.Dup ⟨1, by decide⟩),
   opAt 3100 .GT,
   pushAt 3101 2 4273,
   opAt 3102 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3103 .POP,
   pushAt 3104 2 8224,
   opAt 3105 .MLOAD,
   opAt 3106 (.Dup ⟨1, by decide⟩),
   opAt 3107 .ADD,
   opAt 3108 (.Dup ⟨0, by decide⟩),
   pushAt 3109 2 8224,
   opAt 3110 .MSTORE,
   opAt 3111 .LT,
   opAt 3112 .ISZERO,
   pushAt 3113 2 4267,
   opAt 3114 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3115 .JUMPDEST,
   pushAt 3116 2 8224,
   opAt 3117 .MLOAD,
   opAt 3118 .ISZERO,
   pushAt 3119 2 4402,
   opAt 3120 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3121 0 0,
   pushAt 3122 2 9440,
   opAt 3123 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3124 .JUMPDEST,
   opAt 3125 (.Dup ⟨0, by decide⟩),
   opAt 3126 .MLOAD,
   pushAt 3127 2 8256,
   opAt 3128 (.Dup ⟨2, by decide⟩),
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
   pushAt 3154 2 4349,
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
   pushAt 3162 2 4334,
   opAt 3163 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3164 .JUMPDEST,
   pushAt 3165 2 4413,
   pushAt 3166 2 2048,
   pushAt 3167 2 2288,
   opAt 3168 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3169 .JUMPDEST,
   pushAt 3170 1 1,
   opAt 3171 (.Swap ⟨0, by decide⟩),
   opAt 3172 .SUB,
   pushAt 3173 2 3974,
   opAt 3174 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3175 .JUMPDEST,
   opAt 3176 .POP,
   pushAt 3177 2 1747,
   opAt 3178 .JUMP]

theorem jumpDest4612 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3780 = true :=
  Artifact.isValidJumpDest_index 2767 (by rfl)

theorem jumpDest4656 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3824 = true :=
  Artifact.isValidJumpDest_index 2794 (by rfl)

theorem jumpDest4661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3829 = true :=
  Artifact.isValidJumpDest_index 2797 (by rfl)

theorem jumpDest4668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3836 = true :=
  Artifact.isValidJumpDest_index 2801 (by rfl)

theorem jumpDest4729 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3867 = true :=
  Artifact.isValidJumpDest_index 2825 (by rfl)

theorem jumpDest4843 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3974 = true :=
  Artifact.isValidJumpDest_index 2913 (by rfl)

theorem jumpDest4937 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4090 = true :=
  Artifact.isValidJumpDest_index 2992 (by rfl)

theorem jumpDest5119 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4267 = true :=
  Artifact.isValidJumpDest_index 3063 (by rfl)

theorem jumpDest5125 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4273 = true :=
  Artifact.isValidJumpDest_index 3067 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4334 = true :=
  Artifact.isValidJumpDest_index 3115 (by rfl)

theorem jumpDest5231 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4349 = true :=
  Artifact.isValidJumpDest_index 3124 (by rfl)

theorem jumpDest5315 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4402 = true :=
  Artifact.isValidJumpDest_index 3164 (by rfl)

theorem jumpDest5326 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4413 = true :=
  Artifact.isValidJumpDest_index 3169 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4422 = true :=
  Artifact.isValidJumpDest_index 3175 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
