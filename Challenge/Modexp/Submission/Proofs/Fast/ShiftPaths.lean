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
  [opAt 2748 .JUMPDEST,
   opAt 2749 (.Dup ⟨0, by decide⟩),
   opAt 2750 (.Dup ⟨3, by decide⟩),
   opAt 2751 .EQ,
   pushAt 2752 0 0,
   opAt 2753 .MLOAD,
   pushAt 2754 1 255,
   opAt 2755 .SHR,
   opAt 2756 .AND,
   opAt 2757 .ISZERO,
   pushAt 2758 2 3860,
   opAt 2759 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2760 (.Dup ⟨0, by decide⟩),
   pushAt 2761 1 96,
   pushAt 2762 2 1024,
   opAt 2763 .CALLDATACOPY,
   opAt 2764 (.Dup ⟨0, by decide⟩),
   pushAt 2765 1 96,
   pushAt 2766 2 8256,
   opAt 2767 .CALLDATACOPY,
   pushAt 2768 0 0,
   pushAt 2769 2 8224,
   opAt 2770 .MSTORE,
   pushAt 2771 2 3865,
   pushAt 2772 2 2048,
   pushAt 2773 2 2304,
   opAt 2774 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2775 .JUMPDEST,
   pushAt 2776 2 1533,
   opAt 2777 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2778 .JUMPDEST,
   pushAt 2779 1 1,
   pushAt 2780 2 9408,
   opAt 2781 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2782 .JUMPDEST,
   opAt 2783 (.Dup ⟨0, by decide⟩),
   opAt 2784 .MLOAD,
   opAt 2785 .NOT,
   opAt 2786 (.Dup ⟨2, by decide⟩),
   opAt 2787 .ADD,
   opAt 2788 (.Dup ⟨2, by decide⟩),
   opAt 2789 (.Dup ⟨1, by decide⟩),
   opAt 2790 .LT,
   opAt 2791 (.Swap ⟨2, by decide⟩),
   opAt 2792 .POP,
   opAt 2793 (.Dup ⟨1, by decide⟩),
   pushAt 2794 2 5120,
   opAt 2795 .ADD,
   opAt 2796 .MSTORE,
   opAt 2797 (.Dup ⟨0, by decide⟩),
   opAt 2798 .ISZERO,
   pushAt 2799 2 3903,
   opAt 2800 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2801 1 31, opAt 2802 .NOT,
   opAt 2803 .ADD,
   pushAt 2804 2 3872,
   opAt 2805 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2806 .JUMPDEST,
   opAt 2807 .POP,
   opAt 2808 .POP,
   pushAt 2809 0 0,
   opAt 2810 .MLOAD,
   opAt 2811 (.Dup ⟨0, by decide⟩),
   pushAt 2812 0 0,
   opAt 2813 .SUB,
   opAt 2814 (.Dup ⟨1, by decide⟩),
   opAt 2815 .AND,
   opAt 2816 (.Dup ⟨0, by decide⟩),
   pushAt 2817 2 6144,
   opAt 2818 .MSTORE,
   opAt 2819 (.Dup ⟨0, by decide⟩),
   opAt 2820 (.Dup ⟨2, by decide⟩),
   opAt 2821 .DIV,
   opAt 2822 (.Dup ⟨0, by decide⟩),
   pushAt 2823 2 6176,
   opAt 2824 .MSTORE,
   opAt 2825 (.Dup ⟨1, by decide⟩),
   pushAt 2826 0 0,
   opAt 2827 .SUB,
   opAt 2828 (.Dup ⟨2, by decide⟩),
   opAt 2829 (.Swap ⟨0, by decide⟩),
   opAt 2830 .DIV,
   pushAt 2831 1 1,
   opAt 2832 .ADD,
   pushAt 2833 2 6208,
   opAt 2834 .MSTORE,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   pushAt 2836 0 0,
   opAt 2837 .SUB,
   opAt 2838 (.Dup ⟨1, by decide⟩),
   opAt 2839 (.Swap ⟨0, by decide⟩),
   opAt 2840 .MOD,
   pushAt 2841 2 6240,
   opAt 2842 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2843 (.Dup ⟨0, by decide⟩),
   pushAt 2844 1 3,
   opAt 2845 .MUL,
   pushAt 2846 1 2,
   opAt 2847 .XOR,
   opAt 2848 (.Dup ⟨0, by decide⟩),
   opAt 2849 (.Dup ⟨2, by decide⟩),
   opAt 2850 .MUL,
   pushAt 2851 1 2,
   opAt 2852 .SUB,
   opAt 2853 .MUL,
   opAt 2854 (.Dup ⟨0, by decide⟩),
   opAt 2855 (.Dup ⟨2, by decide⟩),
   opAt 2856 .MUL,
   pushAt 2857 1 2,
   opAt 2858 .SUB,
   opAt 2859 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2860 (.Dup ⟨0, by decide⟩),
   opAt 2861 (.Dup ⟨2, by decide⟩),
   opAt 2862 .MUL,
   pushAt 2863 1 2,
   opAt 2864 .SUB,
   opAt 2865 .MUL,
   opAt 2866 (.Dup ⟨0, by decide⟩),
   opAt 2867 (.Dup ⟨2, by decide⟩),
   opAt 2868 .MUL,
   pushAt 2869 1 2,
   opAt 2870 .SUB,
   opAt 2871 .MUL,
   opAt 2872 (.Dup ⟨0, by decide⟩),
   opAt 2873 (.Dup ⟨2, by decide⟩),
   opAt 2874 .MUL,
   pushAt 2875 1 2,
   opAt 2876 .SUB,
   opAt 2877 .MUL,
   opAt 2878 (.Dup ⟨0, by decide⟩),
   opAt 2879 (.Dup ⟨2, by decide⟩),
   opAt 2880 .MUL,
   pushAt 2881 1 2,
   opAt 2882 .SUB,
   opAt 2883 .MUL,
   pushAt 2884 2 6272,
   opAt 2885 .MSTORE,
   opAt 2886 .POP,
   opAt 2887 .POP,
   opAt 2888 .POP,
   pushAt 2889 1 32,
   opAt 2890 .MLOAD,
   pushAt 2891 1 128,
   opAt 2892 .SHR,
   pushAt 2893 2 6304,
   opAt 2894 .MSTORE,
   opAt 2895 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2896 .JUMPDEST,
   opAt 2897 (.Dup ⟨0, by decide⟩),
   opAt 2898 .ISZERO,
   pushAt 2899 2 4459,
   opAt 2900 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2901 (.Dup ⟨1, by decide⟩),
   pushAt 2902 2 2048,
   pushAt 2903 2 8224,
   opAt 2904 .MCOPY,
   pushAt 2905 0 0,
   pushAt 2906 2 9440,
   opAt 2907 .MLOAD,
   opAt 2908 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2909 2 2048,
   opAt 2910 .MLOAD,
   pushAt 2911 2 6144,
   opAt 2912 .MLOAD,
   opAt 2913 (.Dup ⟨1, by decide⟩),
   pushAt 2914 2 6208,
   opAt 2915 .MLOAD,
   opAt 2916 .MUL,
   opAt 2917 (.Dup ⟨1, by decide⟩),
   pushAt 2918 2 2080,
   opAt 2919 .MLOAD,
   opAt 2920 .DIV,
   opAt 2921 .ADD,
   opAt 2922 (.Swap ⟨1, by decide⟩),
   opAt 2923 .DIV,
   opAt 2924 (.Swap ⟨0, by decide⟩),
   pushAt 2925 2 6176,
   opAt 2926 .MLOAD,
   opAt 2927 (.Dup ⟨0, by decide⟩),
   pushAt 2928 2 6240,
   opAt 2929 .MLOAD,
   opAt 2930 (.Dup ⟨4, by decide⟩),
   opAt 2931 .MULMOD,
   opAt 2932 (.Dup ⟨2, by decide⟩),
   opAt 2933 .ADDMOD,
   opAt 2934 (.Swap ⟨0, by decide⟩),
   opAt 2935 .SUB,
   pushAt 2936 2 6272,
   opAt 2937 .MLOAD,
   opAt 2938 .MUL,
   opAt 2939 (.Dup ⟨0, by decide⟩),
   pushAt 2940 0 0,
   opAt 2941 .MLOAD,
   opAt 2942 .MUL,
   pushAt 2943 2 2080,
   opAt 2944 .MLOAD,
   opAt 2945 .SUB,
   pushAt 2946 2 6304,
   opAt 2947 .MLOAD,
   opAt 2948 (.Dup ⟨2, by decide⟩),
   pushAt 2949 1 128,
   opAt 2950 .SHR,
   opAt 2951 .MUL,
   opAt 2952 .GT,
   opAt 2953 (.Swap ⟨0, by decide⟩),
   opAt 2954 .SUB,
   opAt 2955 (.Swap ⟨0, by decide⟩),
   pushAt 2956 2 6176,
   opAt 2957 .MLOAD,
   opAt 2958 .GT,
   opAt 2959 .ISZERO,
   pushAt 2960 0 0,
   opAt 2961 .SUB,
   opAt 2962 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2963 .JUMPDEST,
   pushAt 2964 0 0,
   pushAt 2965 2 9440,
   opAt 2966 .MLOAD,
   pushAt 2967 2 9408,
   opAt 2968 .MLOAD,
   pushAt 2969 2 5120,
   opAt 2970 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2971 .JUMPDEST,
   opAt 2972 (.Dup ⟨0, by decide⟩),
   opAt 2973 .MLOAD,
   pushAt 2974 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2975 (.Dup ⟨5, by decide⟩),
   opAt 2976 (.Dup ⟨2, by decide⟩),
   opAt 2977 .MUL,
   opAt 2978 (.Swap ⟨1, by decide⟩),
   opAt 2979 (.Dup ⟨6, by decide⟩),
   opAt 2980 .MULMOD,
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 (.Dup ⟨1, by decide⟩),
   opAt 2983 .LT,
   opAt 2984 .SUB,
   opAt 2985 (.Dup ⟨4, by decide⟩),
   opAt 2986 (.Dup ⟨2, by decide⟩),
   opAt 2987 .ADD,
   opAt 2988 (.Dup ⟨0, by decide⟩),
   opAt 2989 (.Swap ⟨5, by decide⟩),
   opAt 2990 .GT,
   opAt 2991 .SUB,
   opAt 2992 .SUB,
   opAt 2993 (.Dup ⟨3, by decide⟩),
   opAt 2994 (.Dup ⟨3, by decide⟩),
   opAt 2995 .MLOAD,
   opAt 2996 .ADD,
   opAt 2997 (.Dup ⟨0, by decide⟩),
   opAt 2998 (.Swap ⟨4, by decide⟩),
   opAt 2999 .GT,
   opAt 3000 .ADD,
   opAt 3001 (.Swap ⟨2, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   pushAt 3003 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3004 .ADD,
   opAt 3005 (.Swap ⟨2, by decide⟩),
   opAt 3006 .MSTORE,
   pushAt 3007 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3008 .ADD,
   pushAt 3009 2 8224,
   opAt 3010 (.Dup ⟨2, by decide⟩),
   opAt 3011 .GT,
   pushAt 3012 2 4126,
   opAt 3013 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3014 .POP,
   opAt 3015 .POP,
   pushAt 3016 2 8224,
   opAt 3017 .MLOAD,
   opAt 3018 (.Dup ⟨1, by decide⟩),
   opAt 3019 .ADD,
   opAt 3020 (.Dup ⟨1, by decide⟩),
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 .LT,
   opAt 3023 (.Swap ⟨1, by decide⟩),
   opAt 3024 .POP,
   opAt 3025 (.Dup ⟨2, by decide⟩),
   opAt 3026 (.Dup ⟨1, by decide⟩),
   opAt 3027 .LT,
   opAt 3028 (.Swap ⟨0, by decide⟩),
   opAt 3029 (.Dup ⟨3, by decide⟩),
   opAt 3030 (.Swap ⟨0, by decide⟩),
   opAt 3031 .SUB,
   opAt 3032 (.Dup ⟨0, by decide⟩),
   pushAt 3033 2 8224,
   opAt 3034 .MSTORE,
   opAt 3035 .POP,
   opAt 3036 .GT,
   opAt 3037 (.Swap ⟨0, by decide⟩),
   opAt 3038 .POP,
   opAt 3039 .ISZERO,
   pushAt 3040 2 4370,
   opAt 3041 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3042 .JUMPDEST,
   pushAt 3043 0 0,
   pushAt 3044 2 9440,
   opAt 3045 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3046 .JUMPDEST,
   opAt 3047 (.Dup ⟨0, by decide⟩),
   opAt 3048 .MLOAD,
   opAt 3049 (.Dup ⟨1, by decide⟩),
   pushAt 3050 2 8256,
   opAt 3051 (.Swap ⟨0, by decide⟩),
   opAt 3052 .SUB,
   opAt 3053 .MLOAD,
   opAt 3054 (.Dup ⟨1, by decide⟩),
   opAt 3055 .ADD,
   opAt 3056 (.Dup ⟨0, by decide⟩),
   opAt 3057 (.Dup ⟨2, by decide⟩),
   opAt 3058 .GT,
   opAt 3059 (.Swap ⟨1, by decide⟩),
   opAt 3060 .POP,
   opAt 3061 (.Dup ⟨3, by decide⟩),
   opAt 3062 .ADD,
   opAt 3063 (.Dup ⟨0, by decide⟩),
   opAt 3064 (.Dup ⟨4, by decide⟩),
   opAt 3065 .GT,
   opAt 3066 (.Swap ⟨3, by decide⟩),
   opAt 3067 .POP,
   opAt 3068 (.Dup ⟨2, by decide⟩),
   opAt 3069 .MSTORE,
   opAt 3070 (.Swap ⟨0, by decide⟩),
   opAt 3071 (.Swap ⟨1, by decide⟩),
   opAt 3072 .OR,
   opAt 3073 (.Swap ⟨0, by decide⟩),
   pushAt 3074 1 31, opAt 3075 .NOT,
   opAt 3076 .ADD,
   pushAt 3077 2 8255,
   opAt 3078 (.Dup ⟨1, by decide⟩),
   opAt 3079 .GT,
   pushAt 3080 2 4309,
   opAt 3081 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3082 .POP,
   pushAt 3083 2 8224,
   opAt 3084 .MLOAD,
   opAt 3085 (.Dup ⟨1, by decide⟩),
   opAt 3086 .ADD,
   opAt 3087 (.Dup ⟨0, by decide⟩),
   pushAt 3088 2 8224,
   opAt 3089 .MSTORE,
   opAt 3090 .LT,
   opAt 3091 .ISZERO,
   pushAt 3092 2 4303,
   opAt 3093 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3094 .JUMPDEST,
   pushAt 3095 2 8224,
   opAt 3096 .MLOAD,
   opAt 3097 .ISZERO,
   pushAt 3098 2 4439,
   opAt 3099 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3100 0 0,
   pushAt 3101 2 9440,
   opAt 3102 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3103 .JUMPDEST,
   opAt 3104 (.Dup ⟨0, by decide⟩),
   opAt 3105 .MLOAD,
   opAt 3106 (.Dup ⟨1, by decide⟩),
   pushAt 3107 2 8256,
   opAt 3108 (.Swap ⟨0, by decide⟩),
   opAt 3109 .SUB,
   opAt 3110 .MLOAD,
   opAt 3111 (.Dup ⟨1, by decide⟩),
   opAt 3112 (.Dup ⟨1, by decide⟩),
   opAt 3113 .GT,
   opAt 3114 (.Swap ⟨1, by decide⟩),
   opAt 3115 .SUB,
   opAt 3116 (.Dup ⟨3, by decide⟩),
   opAt 3117 (.Dup ⟨1, by decide⟩),
   opAt 3118 .LT,
   opAt 3119 (.Swap ⟨0, by decide⟩),
   opAt 3120 (.Dup ⟨4, by decide⟩),
   opAt 3121 (.Swap ⟨0, by decide⟩),
   opAt 3122 .SUB,
   opAt 3123 (.Dup ⟨3, by decide⟩),
   opAt 3124 .MSTORE,
   opAt 3125 .OR,
   opAt 3126 (.Swap ⟨1, by decide⟩),
   opAt 3127 .POP,
   pushAt 3128 1 31, opAt 3129 .NOT,
   opAt 3130 .ADD,
   pushAt 3131 2 8255,
   opAt 3132 (.Dup ⟨1, by decide⟩),
   opAt 3133 .GT,
   pushAt 3134 2 4385,
   opAt 3135 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3136 .POP,
   pushAt 3137 2 8224,
   opAt 3138 .MLOAD,
   opAt 3139 .SUB,
   pushAt 3140 2 8224,
   opAt 3141 .MSTORE,
   pushAt 3142 2 4370,
   opAt 3143 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3144 .JUMPDEST,
   pushAt 3145 2 4450,
   pushAt 3146 2 2048,
   pushAt 3147 2 2304,
   opAt 3148 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3149 .JUMPDEST,
   pushAt 3150 1 1,
   opAt 3151 (.Swap ⟨0, by decide⟩),
   opAt 3152 .SUB,
   pushAt 3153 2 4016,
   opAt 3154 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3155 .JUMPDEST,
   opAt 3156 .POP,
   pushAt 3157 2 1756,
   opAt 3158 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3816 = true :=
  Artifact.isValidJumpDest_index 2748 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3860 = true :=
  Artifact.isValidJumpDest_index 2775 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2778 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3872 = true :=
  Artifact.isValidJumpDest_index 2782 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3903 = true :=
  Artifact.isValidJumpDest_index 2806 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4016 = true :=
  Artifact.isValidJumpDest_index 2896 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4112 = true :=
  Artifact.isValidJumpDest_index 2963 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4126 = true :=
  Artifact.isValidJumpDest_index 2971 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4303 = true :=
  Artifact.isValidJumpDest_index 3042 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4309 = true :=
  Artifact.isValidJumpDest_index 3046 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4370 = true :=
  Artifact.isValidJumpDest_index 3094 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4385 = true :=
  Artifact.isValidJumpDest_index 3103 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4439 = true :=
  Artifact.isValidJumpDest_index 3144 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4450 = true :=
  Artifact.isValidJumpDest_index 3149 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4459 = true :=
  Artifact.isValidJumpDest_index 3155 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
