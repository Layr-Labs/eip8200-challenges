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
  [opAt 2757 .JUMPDEST,
   opAt 2758 (.Dup ⟨0, by decide⟩),
   opAt 2759 (.Dup ⟨3, by decide⟩),
   opAt 2760 .EQ,
   pushAt 2761 0 0,
   opAt 2762 .MLOAD,
   pushAt 2763 1 255,
   opAt 2764 .SHR,
   opAt 2765 .AND,
   opAt 2766 .ISZERO,
   pushAt 2767 2 3889,
   opAt 2768 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2769 (.Dup ⟨0, by decide⟩),
   pushAt 2770 1 96,
   pushAt 2771 2 1024,
   opAt 2772 .CALLDATACOPY,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   pushAt 2774 1 96,
   pushAt 2775 2 8256,
   opAt 2776 .CALLDATACOPY,
   pushAt 2777 0 0,
   pushAt 2778 2 8224,
   opAt 2779 .MSTORE,
   pushAt 2780 2 3894,
   pushAt 2781 2 2048,
   pushAt 2782 2 2225,
   opAt 2783 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2784 .JUMPDEST,
   pushAt 2785 2 1484,
   opAt 2786 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2787 .JUMPDEST,
   pushAt 2788 1 1,
   pushAt 2789 2 9408,
   opAt 2790 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2791 .JUMPDEST,
   opAt 2792 (.Dup ⟨0, by decide⟩),
   opAt 2793 .MLOAD,
   opAt 2794 .NOT,
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .ADD,
   opAt 2797 (.Dup ⟨2, by decide⟩),
   opAt 2798 (.Dup ⟨1, by decide⟩),
   opAt 2799 .LT,
   opAt 2800 (.Swap ⟨2, by decide⟩),
   opAt 2801 .POP,
   opAt 2802 (.Dup ⟨1, by decide⟩),
   pushAt 2803 2 5120,
   opAt 2804 .ADD,
   opAt 2805 .MSTORE,
   opAt 2806 (.Dup ⟨0, by decide⟩),
   opAt 2807 .ISZERO,
   pushAt 2808 2 3932,
   opAt 2809 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2810 1 31,
   opAt 2811 .NOT,
   opAt 2812 .ADD,
   pushAt 2813 2 3901,
   opAt 2814 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2815 .JUMPDEST,
   opAt 2816 .POP,
   opAt 2817 .POP,
   pushAt 2818 0 0,
   opAt 2819 .MLOAD,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   pushAt 2821 0 0,
   opAt 2822 .SUB,
   opAt 2823 (.Dup ⟨1, by decide⟩),
   opAt 2824 .AND,
   opAt 2825 (.Dup ⟨0, by decide⟩),
   pushAt 2826 2 6144,
   opAt 2827 .MSTORE,
   opAt 2828 (.Dup ⟨0, by decide⟩),
   opAt 2829 (.Dup ⟨2, by decide⟩),
   opAt 2830 .DIV,
   opAt 2831 (.Dup ⟨0, by decide⟩),
   pushAt 2832 2 6176,
   opAt 2833 .MSTORE,
   opAt 2834 (.Dup ⟨1, by decide⟩),
   pushAt 2835 0 0,
   opAt 2836 .SUB,
   opAt 2837 (.Dup ⟨2, by decide⟩),
   opAt 2838 (.Swap ⟨0, by decide⟩),
   opAt 2839 .DIV,
   pushAt 2840 1 1,
   opAt 2841 .ADD,
   pushAt 2842 2 6208,
   opAt 2843 .MSTORE,
   opAt 2844 (.Dup ⟨0, by decide⟩),
   pushAt 2845 0 0,
   opAt 2846 .SUB,
   opAt 2847 (.Dup ⟨1, by decide⟩),
   opAt 2848 (.Swap ⟨0, by decide⟩),
   opAt 2849 .MOD,
   pushAt 2850 2 6240,
   opAt 2851 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2852 (.Dup ⟨0, by decide⟩),
   pushAt 2853 1 3,
   opAt 2854 .MUL,
   pushAt 2855 1 2,
   opAt 2856 .XOR,
   opAt 2857 (.Dup ⟨0, by decide⟩),
   opAt 2858 (.Dup ⟨2, by decide⟩),
   opAt 2859 .MUL,
   pushAt 2860 1 2,
   opAt 2861 .SUB,
   opAt 2862 .MUL,
   opAt 2863 (.Dup ⟨0, by decide⟩),
   opAt 2864 (.Dup ⟨2, by decide⟩),
   opAt 2865 .MUL,
   pushAt 2866 1 2,
   opAt 2867 .SUB,
   opAt 2868 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2869 (.Dup ⟨0, by decide⟩),
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
   opAt 2880 .MUL,
   opAt 2881 (.Dup ⟨0, by decide⟩),
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
   pushAt 2893 2 6272,
   opAt 2894 .MSTORE,
   opAt 2895 .POP,
   opAt 2896 .POP,
   opAt 2897 .POP,
   pushAt 2898 1 32,
   opAt 2899 .MLOAD,
   pushAt 2900 1 128,
   opAt 2901 .SHR,
   pushAt 2902 2 6304,
   opAt 2903 .MSTORE,
   opAt 2904 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2905 .JUMPDEST,
   opAt 2906 (.Dup ⟨0, by decide⟩),
   opAt 2907 .ISZERO,
   pushAt 2908 2 4487,
   opAt 2909 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2910 (.Dup ⟨1, by decide⟩),
   pushAt 2911 2 2048,
   pushAt 2912 2 8224,
   opAt 2913 .MCOPY,
   pushAt 2914 0 0,
   pushAt 2915 2 9440,
   opAt 2916 .MLOAD,
   opAt 2917 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2918 2 2048,
   opAt 2919 .MLOAD,
   pushAt 2920 2 6144,
   opAt 2921 .MLOAD,
   opAt 2922 (.Dup ⟨1, by decide⟩),
   pushAt 2923 2 6208,
   opAt 2924 .MLOAD,
   opAt 2925 .MUL,
   opAt 2926 (.Dup ⟨1, by decide⟩),
   pushAt 2927 2 2080,
   opAt 2928 .MLOAD,
   opAt 2929 .DIV,
   opAt 2930 .ADD,
   opAt 2931 (.Swap ⟨1, by decide⟩),
   opAt 2932 .DIV,
   opAt 2933 (.Swap ⟨0, by decide⟩),
   pushAt 2934 2 6176,
   opAt 2935 .MLOAD,
   opAt 2936 (.Dup ⟨0, by decide⟩),
   pushAt 2937 2 6240,
   opAt 2938 .MLOAD,
   opAt 2939 (.Dup ⟨4, by decide⟩),
   opAt 2940 .MULMOD,
   opAt 2941 (.Dup ⟨2, by decide⟩),
   opAt 2942 .ADDMOD,
   opAt 2943 (.Swap ⟨0, by decide⟩),
   opAt 2944 .SUB,
   pushAt 2945 2 6272,
   opAt 2946 .MLOAD,
   opAt 2947 .MUL,
   opAt 2948 (.Dup ⟨0, by decide⟩),
   pushAt 2949 0 0,
   opAt 2950 .MLOAD,
   opAt 2951 .MUL,
   pushAt 2952 2 2080,
   opAt 2953 .MLOAD,
   opAt 2954 .SUB,
   pushAt 2955 2 6304,
   opAt 2956 .MLOAD,
   opAt 2957 (.Dup ⟨2, by decide⟩),
   pushAt 2958 1 128,
   opAt 2959 .SHR,
   opAt 2960 .MUL,
   opAt 2961 .GT,
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
   pushAt 2973 2 9440,
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
   pushAt 3020 2 4154,
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
   pushAt 3048 2 4398,
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
   pushAt 3082 1 31,
   opAt 3083 .NOT,
   opAt 3084 .ADD,
   pushAt 3085 2 8255,
   opAt 3086 (.Dup ⟨1, by decide⟩),
   opAt 3087 .GT,
   pushAt 3088 2 4337,
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
   pushAt 3100 2 4331,
   opAt 3101 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3102 .JUMPDEST,
   pushAt 3103 2 8224,
   opAt 3104 .MLOAD,
   opAt 3105 .ISZERO,
   pushAt 3106 2 4467,
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
   opAt 3114 (.Dup ⟨1, by decide⟩),
   pushAt 3115 2 8256,
   opAt 3116 (.Swap ⟨0, by decide⟩),
   opAt 3117 .SUB,
   opAt 3118 .MLOAD,
   opAt 3119 (.Dup ⟨1, by decide⟩),
   opAt 3120 (.Dup ⟨1, by decide⟩),
   opAt 3121 .GT,
   opAt 3122 (.Swap ⟨1, by decide⟩),
   opAt 3123 .SUB,
   opAt 3124 (.Dup ⟨3, by decide⟩),
   opAt 3125 (.Dup ⟨1, by decide⟩),
   opAt 3126 .LT,
   opAt 3127 (.Swap ⟨0, by decide⟩),
   opAt 3128 (.Dup ⟨4, by decide⟩),
   opAt 3129 (.Swap ⟨0, by decide⟩),
   opAt 3130 .SUB,
   opAt 3131 (.Dup ⟨3, by decide⟩),
   opAt 3132 .MSTORE,
   opAt 3133 .OR,
   opAt 3134 (.Swap ⟨1, by decide⟩),
   opAt 3135 .POP,
   pushAt 3136 1 31,
   opAt 3137 .NOT,
   opAt 3138 .ADD,
   pushAt 3139 2 8255,
   opAt 3140 (.Dup ⟨1, by decide⟩),
   opAt 3141 .GT,
   pushAt 3142 2 4413,
   opAt 3143 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3144 .POP,
   pushAt 3145 2 8224,
   opAt 3146 .MLOAD,
   opAt 3147 .SUB,
   pushAt 3148 2 8224,
   opAt 3149 .MSTORE,
   pushAt 3150 2 4398,
   opAt 3151 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3152 .JUMPDEST,
   pushAt 3153 2 4478,
   pushAt 3154 2 2048,
   pushAt 3155 2 2225,
   opAt 3156 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3157 .JUMPDEST,
   pushAt 3158 1 1,
   opAt 3159 (.Swap ⟨0, by decide⟩),
   opAt 3160 .SUB,
   pushAt 3161 2 4045,
   opAt 3162 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3163 .JUMPDEST,
   opAt 3164 .POP,
   pushAt 3165 2 1692,
   opAt 3166 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3845 = true :=
  Artifact.isValidJumpDest_index 2757 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3889 = true :=
  Artifact.isValidJumpDest_index 2784 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3894 = true :=
  Artifact.isValidJumpDest_index 2787 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3901 = true :=
  Artifact.isValidJumpDest_index 2791 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3932 = true :=
  Artifact.isValidJumpDest_index 2815 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4045 = true :=
  Artifact.isValidJumpDest_index 2905 (by rfl)


theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4154 = true :=
  Artifact.isValidJumpDest_index 2979 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4331 = true :=
  Artifact.isValidJumpDest_index 3050 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4337 = true :=
  Artifact.isValidJumpDest_index 3054 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4398 = true :=
  Artifact.isValidJumpDest_index 3102 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4413 = true :=
  Artifact.isValidJumpDest_index 3111 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4467 = true :=
  Artifact.isValidJumpDest_index 3152 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4478 = true :=
  Artifact.isValidJumpDest_index 3157 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4487 = true :=
  Artifact.isValidJumpDest_index 3163 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
