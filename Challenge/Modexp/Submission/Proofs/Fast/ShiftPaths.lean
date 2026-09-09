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
  [opAt 2764 .JUMPDEST,
   opAt 2765 (.Dup ⟨0, by decide⟩),
   opAt 2766 (.Dup ⟨3, by decide⟩),
   opAt 2767 .EQ,
   pushAt 2768 0 0,
   opAt 2769 .MLOAD,
   pushAt 2770 1 255,
   opAt 2771 .SHR,
   opAt 2772 .AND,
   opAt 2773 .ISZERO,
   pushAt 2774 2 3853,
   opAt 2775 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2776 (.Dup ⟨0, by decide⟩),
   pushAt 2777 1 96,
   pushAt 2778 2 1024,
   opAt 2779 .CALLDATACOPY,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   pushAt 2781 1 96,
   pushAt 2782 2 8256,
   opAt 2783 .CALLDATACOPY,
   pushAt 2784 0 0,
   pushAt 2785 2 8224,
   opAt 2786 .MSTORE,
   pushAt 2787 2 3858,
   pushAt 2788 2 2048,
   pushAt 2789 2 2288,
   opAt 2790 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2791 .JUMPDEST,
   pushAt 2792 2 1528,
   opAt 2793 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2794 .JUMPDEST,
   pushAt 2795 1 1,
   pushAt 2796 2 9408,
   opAt 2797 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2798 .JUMPDEST,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   opAt 2800 .MLOAD,
   opAt 2801 .NOT,
   opAt 2802 (.Dup ⟨2, by decide⟩),
   opAt 2803 .ADD,
   opAt 2804 (.Dup ⟨2, by decide⟩),
   opAt 2805 (.Dup ⟨1, by decide⟩),
   opAt 2806 .LT,
   opAt 2807 (.Swap ⟨2, by decide⟩),
   opAt 2808 .POP,
   opAt 2809 (.Dup ⟨1, by decide⟩),
   pushAt 2810 2 5120,
   opAt 2811 .ADD,
   opAt 2812 .MSTORE,
   opAt 2813 (.Dup ⟨0, by decide⟩),
   opAt 2814 .ISZERO,
   pushAt 2815 2 3896,
   opAt 2816 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2817 1 31, opAt 2818 .NOT,
   opAt 2819 .ADD,
   pushAt 2820 2 3865,
   opAt 2821 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2822 .JUMPDEST,
   opAt 2823 .POP,
   opAt 2824 .POP,
   pushAt 2825 0 0,
   opAt 2826 .MLOAD,
   opAt 2827 (.Dup ⟨0, by decide⟩),
   pushAt 2828 0 0,
   opAt 2829 .SUB,
   opAt 2830 (.Dup ⟨1, by decide⟩),
   opAt 2831 .AND,
   opAt 2832 (.Dup ⟨0, by decide⟩),
   pushAt 2833 2 6144,
   opAt 2834 .MSTORE,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   opAt 2836 (.Dup ⟨2, by decide⟩),
   opAt 2837 .DIV,
   opAt 2838 (.Dup ⟨0, by decide⟩),
   pushAt 2839 2 6176,
   opAt 2840 .MSTORE,
   opAt 2841 (.Dup ⟨1, by decide⟩),
   pushAt 2842 0 0,
   opAt 2843 .SUB,
   opAt 2844 (.Dup ⟨2, by decide⟩),
   opAt 2845 (.Swap ⟨0, by decide⟩),
   opAt 2846 .DIV,
   pushAt 2847 1 1,
   opAt 2848 .ADD,
   pushAt 2849 2 6208,
   opAt 2850 .MSTORE,
   opAt 2851 (.Dup ⟨0, by decide⟩),
   pushAt 2852 0 0,
   opAt 2853 .SUB,
   opAt 2854 (.Dup ⟨1, by decide⟩),
   opAt 2855 (.Swap ⟨0, by decide⟩),
   opAt 2856 .MOD,
   pushAt 2857 2 6240,
   opAt 2858 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2859 (.Dup ⟨0, by decide⟩),
   pushAt 2860 1 2,
   opAt 2861 .SUB,
   opAt 2862 (.Dup ⟨0, by decide⟩),
   opAt 2863 (.Dup ⟨2, by decide⟩),
   opAt 2864 .MUL,
   pushAt 2865 1 2,
   opAt 2866 .SUB,
   opAt 2867 .MUL,
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
   opAt 2909 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2910 .JUMPDEST,
   opAt 2911 (.Dup ⟨0, by decide⟩),
   opAt 2912 .ISZERO,
   pushAt 2913 2 4447,
   opAt 2914 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2915 (.Dup ⟨1, by decide⟩),
   pushAt 2916 2 2048,
   pushAt 2917 2 8224,
   opAt 2918 .MCOPY,
   pushAt 2919 0 0,
   pushAt 2920 2 9440,
   opAt 2921 .MLOAD,
   opAt 2922 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2923 2 2048,
   opAt 2924 .MLOAD,
   pushAt 2925 2 6144,
   opAt 2926 .MLOAD,
   opAt 2927 (.Dup ⟨0, by decide⟩),
   opAt 2928 (.Dup ⟨2, by decide⟩),
   opAt 2929 .DIV,
   opAt 2930 (.Swap ⟨1, by decide⟩),
   opAt 2931 .MOD,
   pushAt 2932 2 6208,
   opAt 2933 .MLOAD,
   opAt 2934 .MUL,
   pushAt 2935 2 2080,
   opAt 2936 .MLOAD,
   pushAt 2937 2 6144,
   opAt 2938 .MLOAD,
   opAt 2939 (.Swap ⟨0, by decide⟩),
   opAt 2940 .DIV,
   opAt 2941 .ADD,
   pushAt 2942 2 6176,
   opAt 2943 .MLOAD,
   opAt 2944 (.Dup ⟨0, by decide⟩),
   pushAt 2945 2 6240,
   opAt 2946 .MLOAD,
   opAt 2947 (.Dup ⟨4, by decide⟩),
   opAt 2948 .MULMOD,
   opAt 2949 (.Dup ⟨2, by decide⟩),
   opAt 2950 .ADDMOD,
   opAt 2951 (.Swap ⟨0, by decide⟩),
   opAt 2952 .SUB,
   pushAt 2953 2 6272,
   opAt 2954 .MLOAD,
   opAt 2955 .MUL,
   opAt 2956 (.Dup ⟨0, by decide⟩),
   pushAt 2957 0 0,
   opAt 2958 .MLOAD,
   opAt 2959 .MUL,
   pushAt 2960 2 2080,
   opAt 2961 .MLOAD,
   opAt 2962 .SUB,
   pushAt 2963 1 32,
   opAt 2964 .MLOAD,
   opAt 2965 .GT,
   opAt 2966 (.Dup ⟨1, by decide⟩),
   pushAt 2967 0 0,
   opAt 2968 .LT,
   opAt 2969 .AND,
   opAt 2970 (.Swap ⟨0, by decide⟩),
   opAt 2971 .SUB,
   opAt 2972 (.Swap ⟨0, by decide⟩),
   pushAt 2973 2 6176,
   opAt 2974 .MLOAD,
   opAt 2975 .GT,
   opAt 2976 .ISZERO,
   pushAt 2977 0 0,
   opAt 2978 .SUB,
   opAt 2979 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2980 0 0,
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
   pushAt 3028 2 4115,
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
   pushAt 3056 2 4359,
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
   pushAt 3096 2 4298,
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
   pushAt 3108 2 4292,
   opAt 3109 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 .JUMPDEST,
   pushAt 3111 2 8224,
   opAt 3112 .MLOAD,
   opAt 3113 .ISZERO,
   pushAt 3114 2 4427,
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
   opAt 3124 .SUB,
   opAt 3125 .MLOAD,
   opAt 3126 (.Dup ⟨1, by decide⟩),
   opAt 3127 (.Dup ⟨1, by decide⟩),
   opAt 3128 .GT,
   opAt 3129 (.Swap ⟨1, by decide⟩),
   opAt 3130 .SUB,
   opAt 3131 (.Dup ⟨3, by decide⟩),
   opAt 3132 (.Dup ⟨1, by decide⟩),
   opAt 3133 .LT,
   opAt 3134 (.Swap ⟨0, by decide⟩),
   opAt 3135 (.Dup ⟨4, by decide⟩),
   opAt 3136 (.Swap ⟨0, by decide⟩),
   opAt 3137 .SUB,
   opAt 3138 (.Dup ⟨3, by decide⟩),
   opAt 3139 .MSTORE,
   opAt 3140 .OR,
   opAt 3141 (.Swap ⟨1, by decide⟩),
   opAt 3142 .POP,
   pushAt 3143 1 31, opAt 3144 .NOT,
   opAt 3145 .ADD,
   pushAt 3146 2 8255,
   opAt 3147 (.Dup ⟨1, by decide⟩),
   opAt 3148 .GT,
   pushAt 3149 2 4374,
   opAt 3150 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3151 .POP,
   pushAt 3152 2 8224,
   opAt 3153 .MLOAD,
   opAt 3154 .SUB,
   pushAt 3155 2 8224,
   opAt 3156 .MSTORE,
   pushAt 3157 2 4359,
   opAt 3158 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3159 .JUMPDEST,
   pushAt 3160 2 4438,
   pushAt 3161 2 2048,
   pushAt 3162 2 2288,
   opAt 3163 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3164 .JUMPDEST,
   pushAt 3165 1 1,
   opAt 3166 (.Swap ⟨0, by decide⟩),
   opAt 3167 .SUB,
   pushAt 3168 2 4003,
   opAt 3169 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3170 .JUMPDEST,
   opAt 3171 .POP,
   pushAt 3172 2 1747,
   opAt 3173 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3809 = true :=
  Artifact.isValidJumpDest_index 2764 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3853 = true :=
  Artifact.isValidJumpDest_index 2791 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3858 = true :=
  Artifact.isValidJumpDest_index 2794 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2798 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3896 = true :=
  Artifact.isValidJumpDest_index 2822 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4003 = true :=
  Artifact.isValidJumpDest_index 2910 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4115 = true :=
  Artifact.isValidJumpDest_index 2987 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4292 = true :=
  Artifact.isValidJumpDest_index 3058 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4298 = true :=
  Artifact.isValidJumpDest_index 3062 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4359 = true :=
  Artifact.isValidJumpDest_index 3110 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4374 = true :=
  Artifact.isValidJumpDest_index 3119 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4427 = true :=
  Artifact.isValidJumpDest_index 3159 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4438 = true :=
  Artifact.isValidJumpDest_index 3164 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4447 = true :=
  Artifact.isValidJumpDest_index 3170 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
