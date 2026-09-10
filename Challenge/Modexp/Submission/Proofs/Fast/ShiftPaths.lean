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
   pushAt 2853 2 2,
   opAt 2854 .SUB,
   opAt 2855 .JUMPDEST,
   opAt 2856 .JUMPDEST,
   opAt 2857 .JUMPDEST,
   opAt 2858 .JUMPDEST,
   opAt 2859 (.Dup ⟨0, by decide⟩),
   opAt 2860 (.Dup ⟨2, by decide⟩),
   opAt 2861 .MUL,
   pushAt 2862 1 2,
   opAt 2863 .SUB,
   opAt 2864 .MUL,
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
   pushAt 2922 2 2048,
   opAt 2923 .MLOAD,
   pushAt 2924 2 6144,
   opAt 2925 .MLOAD,
   opAt 2926 (.Dup ⟨1, by decide⟩),
   opAt 2927 (.Dup ⟨1, by decide⟩),
   opAt 2928 (.Swap ⟨0, by decide⟩),
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
   opAt 2958 .LT,
   opAt 2959 (.Swap ⟨0, by decide⟩),
   opAt 2960 .SUB,
   opAt 2961 (.Swap ⟨0, by decide⟩),
   pushAt 2962 2 6176,
   opAt 2963 .MLOAD,
   opAt 2964 .JUMPDEST,
   opAt 2965 .GT,
   opAt 2966 .ISZERO,
   pushAt 2967 0 0,
   opAt 2968 .SUB,
   opAt 2969 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2970 .JUMPDEST,
   pushAt 2971 0 0,
   pushAt 2972 2 9440,
   opAt 2973 .MLOAD,
   pushAt 2974 2 9408,
   opAt 2975 .MLOAD,
   pushAt 2976 2 5120,
   opAt 2977 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2978 .JUMPDEST,
   opAt 2979 (.Dup ⟨0, by decide⟩),
   opAt 2980 .MLOAD,
   pushAt 2981 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2982 (.Dup ⟨5, by decide⟩),
   opAt 2983 (.Dup ⟨2, by decide⟩),
   opAt 2984 .MUL,
   opAt 2985 (.Swap ⟨1, by decide⟩),
   opAt 2986 (.Dup ⟨6, by decide⟩),
   opAt 2987 .MULMOD,
   opAt 2988 (.Dup ⟨1, by decide⟩),
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 .LT,
   opAt 2991 .SUB,
   opAt 2992 (.Dup ⟨4, by decide⟩),
   opAt 2993 (.Dup ⟨2, by decide⟩),
   opAt 2994 .ADD,
   opAt 2995 (.Dup ⟨0, by decide⟩),
   opAt 2996 (.Swap ⟨5, by decide⟩),
   opAt 2997 .GT,
   opAt 2998 .SUB,
   opAt 2999 .SUB,
   opAt 3000 (.Dup ⟨3, by decide⟩),
   opAt 3001 (.Dup ⟨3, by decide⟩),
   opAt 3002 .MLOAD,
   opAt 3003 .ADD,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 (.Swap ⟨4, by decide⟩),
   opAt 3006 .GT,
   opAt 3007 .ADD,
   opAt 3008 (.Swap ⟨2, by decide⟩),
   opAt 3009 (.Dup ⟨2, by decide⟩),
   pushAt 3010 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3011 .ADD,
   opAt 3012 (.Swap ⟨2, by decide⟩),
   opAt 3013 .MSTORE,
   pushAt 3014 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3015 .ADD,
   pushAt 3016 2 8224,
   opAt 3017 (.Dup ⟨2, by decide⟩),
   opAt 3018 .GT,
   pushAt 3019 2 4119,
   opAt 3020 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3021 .POP,
   opAt 3022 .POP,
   pushAt 3023 2 8224,
   opAt 3024 .MLOAD,
   opAt 3025 (.Dup ⟨1, by decide⟩),
   opAt 3026 .ADD,
   opAt 3027 (.Dup ⟨1, by decide⟩),
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 .LT,
   opAt 3030 (.Swap ⟨1, by decide⟩),
   opAt 3031 .POP,
   opAt 3032 (.Dup ⟨2, by decide⟩),
   opAt 3033 (.Dup ⟨1, by decide⟩),
   opAt 3034 .LT,
   opAt 3035 (.Swap ⟨0, by decide⟩),
   opAt 3036 (.Dup ⟨3, by decide⟩),
   opAt 3037 (.Swap ⟨0, by decide⟩),
   opAt 3038 .SUB,
   opAt 3039 (.Dup ⟨0, by decide⟩),
   pushAt 3040 2 8224,
   opAt 3041 .MSTORE,
   opAt 3042 .POP,
   opAt 3043 .GT,
   opAt 3044 (.Swap ⟨0, by decide⟩),
   opAt 3045 .POP,
   opAt 3046 .ISZERO,
   pushAt 3047 2 4363,
   opAt 3048 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3049 .JUMPDEST,
   pushAt 3050 0 0,
   pushAt 3051 2 9440,
   opAt 3052 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3053 .JUMPDEST,
   opAt 3054 (.Dup ⟨0, by decide⟩),
   opAt 3055 .MLOAD,
   opAt 3056 (.Dup ⟨1, by decide⟩),
   pushAt 3057 2 8256,
   opAt 3058 (.Swap ⟨0, by decide⟩),
   opAt 3059 .SUB,
   opAt 3060 .MLOAD,
   opAt 3061 (.Dup ⟨1, by decide⟩),
   opAt 3062 .ADD,
   opAt 3063 (.Dup ⟨0, by decide⟩),
   opAt 3064 (.Dup ⟨2, by decide⟩),
   opAt 3065 .GT,
   opAt 3066 (.Swap ⟨1, by decide⟩),
   opAt 3067 .POP,
   opAt 3068 (.Dup ⟨3, by decide⟩),
   opAt 3069 .ADD,
   opAt 3070 (.Dup ⟨0, by decide⟩),
   opAt 3071 (.Dup ⟨4, by decide⟩),
   opAt 3072 .GT,
   opAt 3073 (.Swap ⟨3, by decide⟩),
   opAt 3074 .POP,
   opAt 3075 (.Dup ⟨2, by decide⟩),
   opAt 3076 .MSTORE,
   opAt 3077 (.Swap ⟨0, by decide⟩),
   opAt 3078 (.Swap ⟨1, by decide⟩),
   opAt 3079 .OR,
   opAt 3080 (.Swap ⟨0, by decide⟩),
   pushAt 3081 1 31, opAt 3082 .NOT,
   opAt 3083 .ADD,
   pushAt 3084 2 8255,
   opAt 3085 (.Dup ⟨1, by decide⟩),
   opAt 3086 .GT,
   pushAt 3087 2 4302,
   opAt 3088 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3089 .POP,
   pushAt 3090 2 8224,
   opAt 3091 .MLOAD,
   opAt 3092 (.Dup ⟨1, by decide⟩),
   opAt 3093 .ADD,
   opAt 3094 (.Dup ⟨0, by decide⟩),
   pushAt 3095 2 8224,
   opAt 3096 .MSTORE,
   opAt 3097 .LT,
   opAt 3098 .ISZERO,
   pushAt 3099 2 4296,
   opAt 3100 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3101 .JUMPDEST,
   pushAt 3102 2 8224,
   opAt 3103 .MLOAD,
   opAt 3104 .ISZERO,
   pushAt 3105 2 4432,
   opAt 3106 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3107 0 0,
   pushAt 3108 2 9440,
   opAt 3109 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 .JUMPDEST,
   opAt 3111 (.Dup ⟨0, by decide⟩),
   opAt 3112 .MLOAD,
   opAt 3113 (.Dup ⟨1, by decide⟩),
   pushAt 3114 2 8256,
   opAt 3115 (.Swap ⟨0, by decide⟩),
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
  Artifact.isValidJumpDest_index 2970 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4119 = true :=
  Artifact.isValidJumpDest_index 2978 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4296 = true :=
  Artifact.isValidJumpDest_index 3049 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4302 = true :=
  Artifact.isValidJumpDest_index 3053 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4363 = true :=
  Artifact.isValidJumpDest_index 3101 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4378 = true :=
  Artifact.isValidJumpDest_index 3110 (by rfl)

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
