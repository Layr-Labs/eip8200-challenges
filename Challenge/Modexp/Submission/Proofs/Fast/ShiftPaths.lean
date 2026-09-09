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
   pushAt 2914 2 4422,
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
   pushAt 2966 1 128,
   opAt 2967 .SHR,
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
  [pushAt 2983 0 0,
   pushAt 2984 2 9440,
   opAt 2985 .MLOAD,
   pushAt 2986 2 9408,
   opAt 2987 .MLOAD,
   pushAt 2988 2 5120,
   opAt 2989 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2990 .JUMPDEST,
   opAt 2991 (.Dup ⟨0, by decide⟩),
   opAt 2992 .MLOAD,
   pushAt 2993 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2994 (.Dup ⟨5, by decide⟩),
   opAt 2995 (.Dup ⟨2, by decide⟩),
   opAt 2996 .MUL,
   opAt 2997 (.Swap ⟨1, by decide⟩),
   opAt 2998 (.Dup ⟨6, by decide⟩),
   opAt 2999 .MULMOD,
   opAt 3000 (.Dup ⟨1, by decide⟩),
   opAt 3001 (.Dup ⟨1, by decide⟩),
   opAt 3002 .LT,
   opAt 3003 .SUB,
   opAt 3004 (.Dup ⟨4, by decide⟩),
   opAt 3005 (.Dup ⟨2, by decide⟩),
   opAt 3006 .ADD,
   opAt 3007 (.Dup ⟨0, by decide⟩),
   opAt 3008 (.Swap ⟨5, by decide⟩),
   opAt 3009 .GT,
   opAt 3010 .SUB,
   opAt 3011 .SUB,
   opAt 3012 (.Dup ⟨3, by decide⟩),
   opAt 3013 (.Dup ⟨3, by decide⟩),
   opAt 3014 .MLOAD,
   opAt 3015 .ADD,
   opAt 3016 (.Dup ⟨0, by decide⟩),
   opAt 3017 (.Swap ⟨4, by decide⟩),
   opAt 3018 .GT,
   opAt 3019 .ADD,
   opAt 3020 (.Swap ⟨2, by decide⟩),
   opAt 3021 (.Dup ⟨2, by decide⟩),
   pushAt 3022 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3023 .ADD,
   opAt 3024 (.Swap ⟨2, by decide⟩),
   opAt 3025 .MSTORE,
   pushAt 3026 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3027 .ADD,
   pushAt 3028 2 8224,
   opAt 3029 (.Dup ⟨2, by decide⟩),
   opAt 3030 .GT,
   pushAt 3031 2 4090,
   opAt 3032 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3033 .POP,
   opAt 3034 .POP,
   pushAt 3035 2 8224,
   opAt 3036 .MLOAD,
   opAt 3037 (.Dup ⟨1, by decide⟩),
   opAt 3038 .ADD,
   opAt 3039 (.Dup ⟨1, by decide⟩),
   opAt 3040 (.Dup ⟨1, by decide⟩),
   opAt 3041 .LT,
   opAt 3042 (.Swap ⟨1, by decide⟩),
   opAt 3043 .POP,
   opAt 3044 (.Dup ⟨2, by decide⟩),
   opAt 3045 (.Dup ⟨1, by decide⟩),
   opAt 3046 .LT,
   opAt 3047 (.Swap ⟨0, by decide⟩),
   opAt 3048 (.Dup ⟨3, by decide⟩),
   opAt 3049 (.Swap ⟨0, by decide⟩),
   opAt 3050 .SUB,
   opAt 3051 (.Dup ⟨0, by decide⟩),
   pushAt 3052 2 8224,
   opAt 3053 .MSTORE,
   opAt 3054 .POP,
   opAt 3055 .GT,
   opAt 3056 (.Swap ⟨0, by decide⟩),
   opAt 3057 .POP,
   opAt 3058 .ISZERO,
   pushAt 3059 2 4334,
   opAt 3060 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3061 .JUMPDEST,
   pushAt 3062 0 0,
   pushAt 3063 2 9440,
   opAt 3064 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3065 .JUMPDEST,
   opAt 3066 (.Dup ⟨0, by decide⟩),
   opAt 3067 .MLOAD,
   opAt 3068 (.Dup ⟨1, by decide⟩),
   pushAt 3069 2 8256,
   opAt 3070 (.Swap ⟨0, by decide⟩),
   opAt 3071 .SUB,
   opAt 3072 .MLOAD,
   opAt 3073 (.Dup ⟨1, by decide⟩),
   opAt 3074 .ADD,
   opAt 3075 (.Dup ⟨0, by decide⟩),
   opAt 3076 (.Dup ⟨2, by decide⟩),
   opAt 3077 .GT,
   opAt 3078 (.Swap ⟨1, by decide⟩),
   opAt 3079 .POP,
   opAt 3080 (.Dup ⟨3, by decide⟩),
   opAt 3081 .ADD,
   opAt 3082 (.Dup ⟨0, by decide⟩),
   opAt 3083 (.Dup ⟨4, by decide⟩),
   opAt 3084 .GT,
   opAt 3085 (.Swap ⟨3, by decide⟩),
   opAt 3086 .POP,
   opAt 3087 (.Dup ⟨2, by decide⟩),
   opAt 3088 .MSTORE,
   opAt 3089 (.Swap ⟨0, by decide⟩),
   opAt 3090 (.Swap ⟨1, by decide⟩),
   opAt 3091 .OR,
   opAt 3092 (.Swap ⟨0, by decide⟩),
   pushAt 3093 1 31, opAt 3094 .NOT,
   opAt 3095 .ADD,
   pushAt 3096 2 8255,
   opAt 3097 (.Dup ⟨1, by decide⟩),
   opAt 3098 .GT,
   pushAt 3099 2 4273,
   opAt 3100 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3101 .POP,
   pushAt 3102 2 8224,
   opAt 3103 .MLOAD,
   opAt 3104 (.Dup ⟨1, by decide⟩),
   opAt 3105 .ADD,
   opAt 3106 (.Dup ⟨0, by decide⟩),
   pushAt 3107 2 8224,
   opAt 3108 .MSTORE,
   opAt 3109 .LT,
   opAt 3110 .ISZERO,
   pushAt 3111 2 4267,
   opAt 3112 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3113 .JUMPDEST,
   pushAt 3114 2 8224,
   opAt 3115 .MLOAD,
   opAt 3116 .ISZERO,
   pushAt 3117 2 4402,
   opAt 3118 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3119 0 0,
   pushAt 3120 2 9440,
   opAt 3121 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3122 .JUMPDEST,
   opAt 3123 (.Dup ⟨0, by decide⟩),
   opAt 3124 .MLOAD,
   pushAt 3125 2 8256,
   opAt 3126 (.Dup ⟨2, by decide⟩),
   opAt 3127 .SUB,
   opAt 3128 .MLOAD,
   opAt 3129 (.Dup ⟨1, by decide⟩),
   opAt 3130 (.Dup ⟨1, by decide⟩),
   opAt 3131 .GT,
   opAt 3132 (.Swap ⟨1, by decide⟩),
   opAt 3133 .SUB,
   opAt 3134 (.Dup ⟨3, by decide⟩),
   opAt 3135 (.Dup ⟨1, by decide⟩),
   opAt 3136 .LT,
   opAt 3137 (.Swap ⟨0, by decide⟩),
   opAt 3138 (.Dup ⟨4, by decide⟩),
   opAt 3139 (.Swap ⟨0, by decide⟩),
   opAt 3140 .SUB,
   opAt 3141 (.Dup ⟨3, by decide⟩),
   opAt 3142 .MSTORE,
   opAt 3143 .OR,
   opAt 3144 (.Swap ⟨1, by decide⟩),
   opAt 3145 .POP,
   pushAt 3146 1 31, opAt 3147 .NOT,
   opAt 3148 .ADD,
   pushAt 3149 2 8255,
   opAt 3150 (.Dup ⟨1, by decide⟩),
   opAt 3151 .GT,
   pushAt 3152 2 4349,
   opAt 3153 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3154 .POP,
   pushAt 3155 2 8224,
   opAt 3156 .MLOAD,
   opAt 3157 .SUB,
   pushAt 3158 2 8224,
   opAt 3159 .MSTORE,
   pushAt 3160 2 4334,
   opAt 3161 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3162 .JUMPDEST,
   pushAt 3163 2 4413,
   pushAt 3164 2 2048,
   pushAt 3165 2 2288,
   opAt 3166 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3167 .JUMPDEST,
   pushAt 3168 1 1,
   opAt 3169 (.Swap ⟨0, by decide⟩),
   opAt 3170 .SUB,
   pushAt 3171 2 3974,
   opAt 3172 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3173 .JUMPDEST,
   opAt 3174 .POP,
   pushAt 3175 2 1747,
   opAt 3176 .JUMP]

theorem jumpDest4612 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3780 = true :=
  Artifact.isValidJumpDest_index 2765 (by rfl)

theorem jumpDest4656 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3824 = true :=
  Artifact.isValidJumpDest_index 2792 (by rfl)

theorem jumpDest4661 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3829 = true :=
  Artifact.isValidJumpDest_index 2795 (by rfl)

theorem jumpDest4668 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3836 = true :=
  Artifact.isValidJumpDest_index 2799 (by rfl)

theorem jumpDest4729 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3867 = true :=
  Artifact.isValidJumpDest_index 2823 (by rfl)

theorem jumpDest4843 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3974 = true :=
  Artifact.isValidJumpDest_index 2911 (by rfl)

theorem jumpDest4937 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4090 = true :=
  Artifact.isValidJumpDest_index 2990 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4267 = true :=
  Artifact.isValidJumpDest_index 3061 (by rfl)

theorem jumpDest5125 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4273 = true :=
  Artifact.isValidJumpDest_index 3065 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4334 = true :=
  Artifact.isValidJumpDest_index 3113 (by rfl)

theorem jumpDest5231 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4349 = true :=
  Artifact.isValidJumpDest_index 3122 (by rfl)

theorem jumpDest5315 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4402 = true :=
  Artifact.isValidJumpDest_index 3162 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4413 = true :=
  Artifact.isValidJumpDest_index 3167 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4422 = true :=
  Artifact.isValidJumpDest_index 3173 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
