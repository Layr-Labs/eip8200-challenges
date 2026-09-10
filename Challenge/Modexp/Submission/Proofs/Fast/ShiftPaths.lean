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
  [opAt 2756 .JUMPDEST,
   opAt 2757 (.Dup ⟨0, by decide⟩),
   opAt 2758 (.Dup ⟨3, by decide⟩),
   opAt 2759 .EQ,
   pushAt 2760 0 0,
   opAt 2761 .MLOAD,
   pushAt 2762 1 255,
   opAt 2763 .SHR,
   opAt 2764 .AND,
   opAt 2765 .ISZERO,
   pushAt 2766 2 3860,
   opAt 2767 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2768 (.Dup ⟨0, by decide⟩),
   pushAt 2769 1 96,
   pushAt 2770 2 1024,
   opAt 2771 .CALLDATACOPY,
   opAt 2772 (.Dup ⟨0, by decide⟩),
   pushAt 2773 1 96,
   pushAt 2774 2 8256,
   opAt 2775 .CALLDATACOPY,
   pushAt 2776 0 0,
   pushAt 2777 2 8224,
   opAt 2778 .MSTORE,
   pushAt 2779 2 3865,
   pushAt 2780 2 2048,
   pushAt 2781 2 2304,
   opAt 2782 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2783 .JUMPDEST,
   pushAt 2784 2 1533,
   opAt 2785 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2786 .JUMPDEST,
   pushAt 2787 1 1,
   pushAt 2788 2 9408,
   opAt 2789 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2790 .JUMPDEST,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   opAt 2792 .MLOAD,
   opAt 2793 .NOT,
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .ADD,
   opAt 2796 (.Dup ⟨2, by decide⟩),
   opAt 2797 (.Dup ⟨1, by decide⟩),
   opAt 2798 .LT,
   opAt 2799 (.Swap ⟨2, by decide⟩),
   opAt 2800 .POP,
   opAt 2801 (.Dup ⟨1, by decide⟩),
   pushAt 2802 2 5120,
   opAt 2803 .ADD,
   opAt 2804 .MSTORE,
   opAt 2805 (.Dup ⟨0, by decide⟩),
   opAt 2806 .ISZERO,
   pushAt 2807 2 3903,
   opAt 2808 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2809 1 31, opAt 2810 .NOT,
   opAt 2811 .ADD,
   pushAt 2812 2 3872,
   opAt 2813 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2814 .JUMPDEST,
   opAt 2815 .POP,
   opAt 2816 .POP,
   pushAt 2817 0 0,
   opAt 2818 .MLOAD,
   opAt 2819 (.Dup ⟨0, by decide⟩),
   pushAt 2820 0 0,
   opAt 2821 .SUB,
   opAt 2822 (.Dup ⟨1, by decide⟩),
   opAt 2823 .AND,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   pushAt 2825 2 6144,
   opAt 2826 .MSTORE,
   opAt 2827 (.Dup ⟨0, by decide⟩),
   opAt 2828 (.Dup ⟨2, by decide⟩),
   opAt 2829 .DIV,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   pushAt 2831 2 6176,
   opAt 2832 .MSTORE,
   opAt 2833 (.Dup ⟨1, by decide⟩),
   pushAt 2834 0 0,
   opAt 2835 .SUB,
   opAt 2836 (.Dup ⟨2, by decide⟩),
   opAt 2837 (.Swap ⟨0, by decide⟩),
   opAt 2838 .DIV,
   pushAt 2839 1 1,
   opAt 2840 .ADD,
   pushAt 2841 2 6208,
   opAt 2842 .MSTORE,
   opAt 2843 (.Dup ⟨0, by decide⟩),
   pushAt 2844 0 0,
   opAt 2845 .SUB,
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 (.Swap ⟨0, by decide⟩),
   opAt 2848 .MOD,
   pushAt 2849 2 6240,
   opAt 2850 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2851 .JUMPDEST,
   opAt 2852 (.Dup ⟨0, by decide⟩),
   pushAt 2853 2 3,
   opAt 2854 .MUL,
   pushAt 2855 1 2,
   opAt 2856 .XOR,
   opAt 2857 .JUMPDEST,
   opAt 2858 .JUMPDEST,
   opAt 2859 .JUMPDEST,
   opAt 2860 .JUMPDEST,
   opAt 2861 .JUMPDEST,
   opAt 2862 .JUMPDEST,
   opAt 2863 .JUMPDEST,
   opAt 2864 .JUMPDEST,
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
   opAt 2876 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2877 .JUMPDEST,
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
   opAt 2895 .MUL,
   opAt 2896 (.Dup ⟨0, by decide⟩),
   opAt 2897 (.Dup ⟨2, by decide⟩),
   opAt 2898 .MUL,
   pushAt 2899 1 2,
   opAt 2900 .SUB,
   opAt 2901 .MUL,
   pushAt 2902 2 6272,
   opAt 2903 .MSTORE,
   opAt 2904 .POP,
   opAt 2905 .POP,
   opAt 2906 .POP,
   opAt 2907 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2908 .JUMPDEST,
   opAt 2909 (.Dup ⟨0, by decide⟩),
   opAt 2910 .ISZERO,
   pushAt 2911 2 4452,
   opAt 2912 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2913 (.Dup ⟨1, by decide⟩),
   pushAt 2914 2 2048,
   pushAt 2915 2 8224,
   opAt 2916 .MCOPY,
   pushAt 2917 0 0,
   pushAt 2918 2 9440,
   opAt 2919 .MLOAD,
   opAt 2920 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2921 .JUMPDEST,
   pushAt 2922 8 2048,
   opAt 2923 .MLOAD,
   pushAt 2924 2 6144,
   opAt 2925 .MLOAD,
   opAt 2926 (.Dup ⟨1, by decide⟩),
   pushAt 2927 2 6208,
   opAt 2928 .MLOAD,
   opAt 2929 .MUL,
   opAt 2930 (.Dup ⟨1, by decide⟩),
   pushAt 2931 2 2080,
   opAt 2932 .MLOAD,
   opAt 2933 .DIV,
   opAt 2934 .ADD,
   opAt 2935 (.Swap ⟨1, by decide⟩),
   opAt 2936 .DIV,
   opAt 2937 (.Swap ⟨0, by decide⟩),
   pushAt 2938 2 6176,
   opAt 2939 .MLOAD,
   opAt 2940 (.Dup ⟨0, by decide⟩),
   pushAt 2941 2 6240,
   opAt 2942 .MLOAD,
   opAt 2943 (.Dup ⟨4, by decide⟩),
   opAt 2944 .MULMOD,
   opAt 2945 (.Dup ⟨2, by decide⟩),

   opAt 2946 .ADDMOD,
   opAt 2947 (.Swap ⟨0, by decide⟩),
   opAt 2948 .SUB,
   pushAt 2949 2 6272,
   opAt 2950 .MLOAD,
   opAt 2951 .MUL,
   opAt 2952 (.Dup ⟨0, by decide⟩),
   pushAt 2953 0 0,
   opAt 2954 .LT,
   opAt 2955 (.Swap ⟨0, by decide⟩),
   opAt 2956 .SUB,
   opAt 2957 (.Swap ⟨0, by decide⟩),
   pushAt 2958 2 6176,
   opAt 2959 .MLOAD,
   opAt 2960 .JUMPDEST,
   opAt 2961 .GT,
   opAt 2962 .ISZERO,
   pushAt 2963 0 0,
   opAt 2964 .SUB,
   opAt 2965 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2966 .JUMPDEST,
   pushAt 2967 0 0,
   pushAt 2968 2 9440,
   opAt 2969 .MLOAD,
   pushAt 2970 2 9408,
   opAt 2971 .MLOAD,
   pushAt 2972 2 5120,
   opAt 2973 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2974 .JUMPDEST,
   opAt 2975 (.Dup ⟨0, by decide⟩),
   opAt 2976 .MLOAD,
   pushAt 2977 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2978 (.Dup ⟨5, by decide⟩),
   opAt 2979 (.Dup ⟨2, by decide⟩),
   opAt 2980 .MUL,
   opAt 2981 (.Swap ⟨1, by decide⟩),
   opAt 2982 (.Dup ⟨6, by decide⟩),
   opAt 2983 .MULMOD,
   opAt 2984 (.Dup ⟨1, by decide⟩),
   opAt 2985 (.Dup ⟨1, by decide⟩),
   opAt 2986 .LT,
   opAt 2987 .SUB,
   opAt 2988 (.Dup ⟨4, by decide⟩),
   opAt 2989 (.Dup ⟨2, by decide⟩),
   opAt 2990 .ADD,
   opAt 2991 (.Dup ⟨0, by decide⟩),
   opAt 2992 (.Swap ⟨5, by decide⟩),
   opAt 2993 .GT,
   opAt 2994 .SUB,
   opAt 2995 .SUB,
   opAt 2996 (.Dup ⟨3, by decide⟩),
   opAt 2997 (.Dup ⟨3, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 .ADD,
   opAt 3000 (.Dup ⟨0, by decide⟩),
   opAt 3001 (.Swap ⟨4, by decide⟩),
   opAt 3002 .GT,
   opAt 3003 .ADD,
   opAt 3004 (.Swap ⟨2, by decide⟩),
   opAt 3005 (.Dup ⟨2, by decide⟩),
   pushAt 3006 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3007 .ADD,
   opAt 3008 (.Swap ⟨2, by decide⟩),
   opAt 3009 .MSTORE,
   pushAt 3010 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3011 .ADD,
   pushAt 3012 2 8224,
   opAt 3013 (.Dup ⟨2, by decide⟩),
   opAt 3014 .GT,
   pushAt 3015 2 4119,
   opAt 3016 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3017 .POP,
   opAt 3018 .POP,
   pushAt 3019 2 8224,
   opAt 3020 .MLOAD,
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 .ADD,
   opAt 3023 (.Dup ⟨1, by decide⟩),
   opAt 3024 (.Dup ⟨1, by decide⟩),
   opAt 3025 .LT,
   opAt 3026 (.Swap ⟨1, by decide⟩),
   opAt 3027 .POP,
   opAt 3028 (.Dup ⟨2, by decide⟩),
   opAt 3029 (.Dup ⟨1, by decide⟩),
   opAt 3030 .LT,
   opAt 3031 (.Swap ⟨0, by decide⟩),
   opAt 3032 (.Dup ⟨3, by decide⟩),
   opAt 3033 (.Swap ⟨0, by decide⟩),
   opAt 3034 .SUB,
   opAt 3035 (.Dup ⟨0, by decide⟩),
   pushAt 3036 2 8224,
   opAt 3037 .MSTORE,
   opAt 3038 .POP,
   opAt 3039 .GT,
   opAt 3040 (.Swap ⟨0, by decide⟩),
   opAt 3041 .POP,
   opAt 3042 .ISZERO,
   pushAt 3043 2 4363,
   opAt 3044 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3045 .JUMPDEST,
   pushAt 3046 0 0,
   pushAt 3047 2 9440,
   opAt 3048 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3049 .JUMPDEST,
   opAt 3050 (.Dup ⟨0, by decide⟩),
   opAt 3051 .MLOAD,
   opAt 3052 (.Dup ⟨1, by decide⟩),
   pushAt 3053 2 8256,
   opAt 3054 (.Swap ⟨0, by decide⟩),
   opAt 3055 .SUB,
   opAt 3056 .MLOAD,
   opAt 3057 (.Dup ⟨1, by decide⟩),
   opAt 3058 .ADD,
   opAt 3059 (.Dup ⟨0, by decide⟩),
   opAt 3060 (.Dup ⟨2, by decide⟩),
   opAt 3061 .GT,
   opAt 3062 (.Swap ⟨1, by decide⟩),
   opAt 3063 .POP,
   opAt 3064 (.Dup ⟨3, by decide⟩),
   opAt 3065 .ADD,
   opAt 3066 (.Dup ⟨0, by decide⟩),
   opAt 3067 (.Dup ⟨4, by decide⟩),
   opAt 3068 .GT,
   opAt 3069 (.Swap ⟨3, by decide⟩),
   opAt 3070 .POP,
   opAt 3071 (.Dup ⟨2, by decide⟩),
   opAt 3072 .MSTORE,
   opAt 3073 (.Swap ⟨0, by decide⟩),
   opAt 3074 (.Swap ⟨1, by decide⟩),
   opAt 3075 .OR,
   opAt 3076 (.Swap ⟨0, by decide⟩),
   pushAt 3077 1 31, opAt 3078 .NOT,
   opAt 3079 .ADD,
   pushAt 3080 2 8255,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 .GT,
   pushAt 3083 2 4302,
   opAt 3084 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3085 .POP,
   pushAt 3086 2 8224,
   opAt 3087 .MLOAD,
   opAt 3088 (.Dup ⟨1, by decide⟩),
   opAt 3089 .ADD,
   opAt 3090 (.Dup ⟨0, by decide⟩),
   pushAt 3091 2 8224,
   opAt 3092 .MSTORE,
   opAt 3093 .LT,
   opAt 3094 .ISZERO,
   pushAt 3095 2 4296,
   opAt 3096 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3097 .JUMPDEST,
   pushAt 3098 2 8224,
   opAt 3099 .MLOAD,
   opAt 3100 .ISZERO,
   pushAt 3101 2 4432,
   opAt 3102 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3103 0 0,
   pushAt 3104 2 9440,
   opAt 3105 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3106 .JUMPDEST,
   opAt 3107 (.Dup ⟨0, by decide⟩),
   opAt 3108 .MLOAD,
   opAt 3109 (.Dup ⟨1, by decide⟩),
   pushAt 3110 2 8256,
   opAt 3111 (.Swap ⟨0, by decide⟩),
   opAt 3112 .SUB,
   opAt 3113 .MLOAD,
   opAt 3114 (.Dup ⟨1, by decide⟩),
   opAt 3115 (.Dup ⟨1, by decide⟩),
   opAt 3116 .GT,
   opAt 3117 (.Swap ⟨1, by decide⟩),
   opAt 3118 .SUB,
   opAt 3119 (.Dup ⟨3, by decide⟩),
   opAt 3120 (.Dup ⟨1, by decide⟩),
   opAt 3121 .LT,
   opAt 3122 (.Swap ⟨0, by decide⟩),
   opAt 3123 (.Dup ⟨4, by decide⟩),
   opAt 3124 (.Swap ⟨0, by decide⟩),
   opAt 3125 .SUB,
   opAt 3126 (.Dup ⟨3, by decide⟩),
   opAt 3127 .MSTORE,
   opAt 3128 .OR,
   opAt 3129 (.Swap ⟨1, by decide⟩),
   opAt 3130 .POP,
   pushAt 3131 1 31, opAt 3132 .NOT,
   opAt 3133 .ADD,
   pushAt 3134 2 8255,
   opAt 3135 (.Dup ⟨1, by decide⟩),
   opAt 3136 .GT,
   pushAt 3137 2 4378,
   opAt 3138 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3139 .POP,
   pushAt 3140 2 8224,
   opAt 3141 .MLOAD,
   opAt 3142 .SUB,
   pushAt 3143 2 8224,
   opAt 3144 .MSTORE,
   pushAt 3145 2 4363,
   opAt 3146 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3147 .JUMPDEST,
   pushAt 3148 2 4443,
   pushAt 3149 2 2048,
   pushAt 3150 2 2304,
   opAt 3151 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3152 .JUMPDEST,
   pushAt 3153 1 1,
   opAt 3154 (.Swap ⟨0, by decide⟩),
   opAt 3155 .SUB,
   pushAt 3156 2 4017,
   opAt 3157 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3158 .JUMPDEST,
   opAt 3159 .POP,
   pushAt 3160 2 1756,
   opAt 3161 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3816 = true :=
  Artifact.isValidJumpDest_index 2756 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3860 = true :=
  Artifact.isValidJumpDest_index 2783 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2786 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3872 = true :=
  Artifact.isValidJumpDest_index 2790 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3903 = true :=
  Artifact.isValidJumpDest_index 2814 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3949 = true :=
  Artifact.isValidJumpDest_index 2851 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3980 = true :=
  Artifact.isValidJumpDest_index 2877 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4017 = true :=
  Artifact.isValidJumpDest_index 2908 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4038 = true :=
  Artifact.isValidJumpDest_index 2921 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4105 = true :=
  Artifact.isValidJumpDest_index 2966 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4119 = true :=
  Artifact.isValidJumpDest_index 2974 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4296 = true :=
  Artifact.isValidJumpDest_index 3045 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4302 = true :=
  Artifact.isValidJumpDest_index 3049 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4363 = true :=
  Artifact.isValidJumpDest_index 3097 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4378 = true :=
  Artifact.isValidJumpDest_index 3106 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4432 = true :=
  Artifact.isValidJumpDest_index 3147 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4443 = true :=
  Artifact.isValidJumpDest_index 3152 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4452 = true :=
  Artifact.isValidJumpDest_index 3158 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
