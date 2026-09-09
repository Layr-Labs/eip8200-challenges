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
   pushAt 2777 2 3860,
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
   pushAt 2790 2 3865,
   pushAt 2791 2 2048,
   pushAt 2792 2 2304,
   opAt 2793 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2794 .JUMPDEST,
   pushAt 2795 2 1533,
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
   pushAt 2818 2 3903,
   opAt 2819 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2820 1 31, opAt 2821 .NOT,
   opAt 2822 .ADD,
   pushAt 2823 2 3872,
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
   pushAt 2863 7 2,
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
   pushAt 2886 2 2,
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
   pushAt 2916 2 4452,
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
  [pushAt 2926 4 2048,
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
   opAt 2961 .LT,
   opAt 2962 (.Swap ⟨0, by decide⟩),
   opAt 2963 .SUB,
   opAt 2964 (.Swap ⟨0, by decide⟩),
   pushAt 2965 2 6176,
   opAt 2966 .MLOAD,
   opAt 2967 .GT,
   opAt 2968 .ISZERO,
   pushAt 2969 0 0,
   opAt 2970 .SUB,
   opAt 2971 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2972 0 0,
   pushAt 2973 4 9440,
   opAt 2974 .MLOAD,
   pushAt 2975 2 9408,
   opAt 2976 .MLOAD,
   pushAt 2977 2 5120,
   opAt 2978 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2979 .JUMPDEST,
   opAt 2980 (.Dup ⟨0, by decide⟩),
   opAt 2981 .MLOAD,
   pushAt 2982 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2983 (.Dup ⟨5, by decide⟩),
   opAt 2984 (.Dup ⟨2, by decide⟩),
   opAt 2985 .MUL,
   opAt 2986 (.Swap ⟨1, by decide⟩),
   opAt 2987 (.Dup ⟨6, by decide⟩),
   opAt 2988 .MULMOD,
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 (.Dup ⟨1, by decide⟩),
   opAt 2991 .LT,
   opAt 2992 .SUB,
   opAt 2993 (.Dup ⟨4, by decide⟩),
   opAt 2994 (.Dup ⟨2, by decide⟩),
   opAt 2995 .ADD,
   opAt 2996 (.Dup ⟨0, by decide⟩),
   opAt 2997 (.Swap ⟨5, by decide⟩),
   opAt 2998 .GT,
   opAt 2999 .SUB,
   opAt 3000 .SUB,
   opAt 3001 (.Dup ⟨3, by decide⟩),
   opAt 3002 (.Dup ⟨3, by decide⟩),
   opAt 3003 .MLOAD,
   opAt 3004 .ADD,
   opAt 3005 (.Dup ⟨0, by decide⟩),
   opAt 3006 (.Swap ⟨4, by decide⟩),
   opAt 3007 .GT,
   opAt 3008 .ADD,
   opAt 3009 (.Swap ⟨2, by decide⟩),
   opAt 3010 (.Dup ⟨2, by decide⟩),
   pushAt 3011 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3012 .ADD,
   opAt 3013 (.Swap ⟨2, by decide⟩),
   opAt 3014 .MSTORE,
   pushAt 3015 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3016 .ADD,
   pushAt 3017 2 8224,
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .GT,
   pushAt 3020 2 4119,
   opAt 3021 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3022 .POP,
   opAt 3023 .POP,
   pushAt 3024 2 8224,
   opAt 3025 .MLOAD,
   opAt 3026 (.Dup ⟨1, by decide⟩),
   opAt 3027 .ADD,
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 (.Dup ⟨1, by decide⟩),
   opAt 3030 .LT,
   opAt 3031 (.Swap ⟨1, by decide⟩),
   opAt 3032 .POP,
   opAt 3033 (.Dup ⟨2, by decide⟩),
   opAt 3034 (.Dup ⟨1, by decide⟩),
   opAt 3035 .LT,
   opAt 3036 (.Swap ⟨0, by decide⟩),
   opAt 3037 (.Dup ⟨3, by decide⟩),
   opAt 3038 (.Swap ⟨0, by decide⟩),
   opAt 3039 .SUB,
   opAt 3040 (.Dup ⟨0, by decide⟩),
   pushAt 3041 2 8224,
   opAt 3042 .MSTORE,
   opAt 3043 .POP,
   opAt 3044 .GT,
   opAt 3045 (.Swap ⟨0, by decide⟩),
   opAt 3046 .POP,
   opAt 3047 .ISZERO,
   pushAt 3048 2 4363,
   opAt 3049 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3050 .JUMPDEST,
   pushAt 3051 0 0,
   pushAt 3052 2 9440,
   opAt 3053 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3054 .JUMPDEST,
   opAt 3055 (.Dup ⟨0, by decide⟩),
   opAt 3056 .MLOAD,
   opAt 3057 (.Dup ⟨1, by decide⟩),
   pushAt 3058 2 8256,
   opAt 3059 (.Swap ⟨0, by decide⟩),
   opAt 3060 .SUB,
   opAt 3061 .MLOAD,
   opAt 3062 (.Dup ⟨1, by decide⟩),
   opAt 3063 .ADD,
   opAt 3064 (.Dup ⟨0, by decide⟩),
   opAt 3065 (.Dup ⟨2, by decide⟩),
   opAt 3066 .GT,
   opAt 3067 (.Swap ⟨1, by decide⟩),
   opAt 3068 .POP,
   opAt 3069 (.Dup ⟨3, by decide⟩),
   opAt 3070 .ADD,
   opAt 3071 (.Dup ⟨0, by decide⟩),
   opAt 3072 (.Dup ⟨4, by decide⟩),
   opAt 3073 .GT,
   opAt 3074 (.Swap ⟨3, by decide⟩),
   opAt 3075 .POP,
   opAt 3076 (.Dup ⟨2, by decide⟩),
   opAt 3077 .MSTORE,
   opAt 3078 (.Swap ⟨0, by decide⟩),
   opAt 3079 (.Swap ⟨1, by decide⟩),
   opAt 3080 .OR,
   opAt 3081 (.Swap ⟨0, by decide⟩),
   pushAt 3082 1 31, opAt 3083 .NOT,
   opAt 3084 .ADD,
   pushAt 3085 2 8255,
   opAt 3086 (.Dup ⟨1, by decide⟩),
   opAt 3087 .GT,
   pushAt 3088 2 4302,
   opAt 3089 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3090 .POP,
   pushAt 3091 2 8224,
   opAt 3092 .MLOAD,
   opAt 3093 (.Dup ⟨1, by decide⟩),
   opAt 3094 .ADD,
   opAt 3095 (.Dup ⟨0, by decide⟩),
   pushAt 3096 2 8224,
   opAt 3097 .MSTORE,
   opAt 3098 .LT,
   opAt 3099 .ISZERO,
   pushAt 3100 2 4296,
   opAt 3101 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3102 .JUMPDEST,
   pushAt 3103 2 8224,
   opAt 3104 .MLOAD,
   opAt 3105 .ISZERO,
   pushAt 3106 2 4432,
   opAt 3107 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3108 0 0,
   pushAt 3109 2 9440,
   opAt 3110 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3111 .JUMPDEST,
   opAt 3112 (.Dup ⟨0, by decide⟩),
   opAt 3113 .MLOAD,
   pushAt 3114 3 8256,
   opAt 3115 (.Dup ⟨2, by decide⟩),
   opAt 3116 .SUB,
   opAt 3117 .MLOAD,
   opAt 3118 (.Dup ⟨1, by decide⟩),
   opAt 3119 (.Dup ⟨1, by decide⟩),
   opAt 3120 .GT,
   opAt 3121 (.Swap ⟨1, by decide⟩),
   opAt 3122 .SUB,
   opAt 3123 (.Dup ⟨3, by decide⟩),
   opAt 3124 (.Dup ⟨1, by decide⟩),
   opAt 3125 .LT,
   opAt 3126 (.Swap ⟨0, by decide⟩),
   opAt 3127 (.Dup ⟨4, by decide⟩),
   opAt 3128 (.Swap ⟨0, by decide⟩),
   opAt 3129 .SUB,
   opAt 3130 (.Dup ⟨3, by decide⟩),
   opAt 3131 .MSTORE,
   opAt 3132 .OR,
   opAt 3133 (.Swap ⟨1, by decide⟩),
   opAt 3134 .POP,
   pushAt 3135 1 31, opAt 3136 .NOT,
   opAt 3137 .ADD,
   pushAt 3138 2 8255,
   opAt 3139 (.Dup ⟨1, by decide⟩),
   opAt 3140 .GT,
   pushAt 3141 2 4378,
   opAt 3142 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3143 .POP,
   pushAt 3144 2 8224,
   opAt 3145 .MLOAD,
   opAt 3146 .SUB,
   pushAt 3147 2 8224,
   opAt 3148 .MSTORE,
   pushAt 3149 2 4363,
   opAt 3150 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3151 .JUMPDEST,
   pushAt 3152 2 4443,
   pushAt 3153 2 2048,
   pushAt 3154 2 2304,
   opAt 3155 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3156 .JUMPDEST,
   pushAt 3157 1 1,
   opAt 3158 (.Swap ⟨0, by decide⟩),
   opAt 3159 .SUB,
   pushAt 3160 2 4017,
   opAt 3161 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3162 .JUMPDEST,
   opAt 3163 .POP,
   pushAt 3164 2 1756,
   opAt 3165 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3816 = true :=
  Artifact.isValidJumpDest_index 2767 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3860 = true :=
  Artifact.isValidJumpDest_index 2794 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2797 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3872 = true :=
  Artifact.isValidJumpDest_index 2801 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3903 = true :=
  Artifact.isValidJumpDest_index 2825 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4017 = true :=
  Artifact.isValidJumpDest_index 2913 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4119 = true :=
  Artifact.isValidJumpDest_index 2979 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4296 = true :=
  Artifact.isValidJumpDest_index 3050 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4302 = true :=
  Artifact.isValidJumpDest_index 3054 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4363 = true :=
  Artifact.isValidJumpDest_index 3102 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4378 = true :=
  Artifact.isValidJumpDest_index 3111 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4432 = true :=
  Artifact.isValidJumpDest_index 3151 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4443 = true :=
  Artifact.isValidJumpDest_index 3156 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4452 = true :=
  Artifact.isValidJumpDest_index 3162 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
