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
  [opAt 2755 .JUMPDEST,
   opAt 2756 (.Dup ⟨0, by decide⟩),
   opAt 2757 (.Dup ⟨3, by decide⟩),
   opAt 2758 .EQ,
   pushAt 2759 0 0,
   opAt 2760 .MLOAD,
   pushAt 2761 1 255,
   opAt 2762 .SHR,
   opAt 2763 .AND,
   opAt 2764 .ISZERO,
   pushAt 2765 2 3839,
   opAt 2766 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2767 (.Dup ⟨0, by decide⟩),
   pushAt 2768 1 96,
   pushAt 2769 2 1024,
   opAt 2770 .CALLDATACOPY,
   opAt 2771 (.Dup ⟨0, by decide⟩),
   pushAt 2772 1 96,
   pushAt 2773 2 8256,
   opAt 2774 .CALLDATACOPY,
   pushAt 2775 0 0,
   pushAt 2776 2 8224,
   opAt 2777 .MSTORE,
   pushAt 2778 2 3844,
   pushAt 2779 2 2048,
   pushAt 2780 2 2292,
   opAt 2781 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2782 .JUMPDEST,
   pushAt 2783 2 1527,
   opAt 2784 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2785 .JUMPDEST,
   pushAt 2786 1 1,
   pushAt 2787 2 9408,
   opAt 2788 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2789 .JUMPDEST,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   opAt 2791 .MLOAD,
   opAt 2792 .NOT,
   opAt 2793 (.Dup ⟨2, by decide⟩),
   opAt 2794 .ADD,
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 (.Dup ⟨1, by decide⟩),
   opAt 2797 .LT,
   opAt 2798 (.Swap ⟨2, by decide⟩),
   opAt 2799 .POP,
   opAt 2800 (.Dup ⟨1, by decide⟩),
   pushAt 2801 2 5120,
   opAt 2802 .ADD,
   opAt 2803 .MSTORE,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   opAt 2805 .ISZERO,
   pushAt 2806 2 3882,
   opAt 2807 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2808 1 31, opAt 2809 .NOT,
   opAt 2810 .ADD,
   pushAt 2811 2 3851,
   opAt 2812 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2813 .JUMPDEST,
   opAt 2814 .POP,
   opAt 2815 .POP,
   pushAt 2816 0 0,
   opAt 2817 .MLOAD,
   opAt 2818 (.Dup ⟨0, by decide⟩),
   pushAt 2819 0 0,
   opAt 2820 .SUB,
   opAt 2821 (.Dup ⟨1, by decide⟩),
   opAt 2822 .AND,
   opAt 2823 (.Dup ⟨0, by decide⟩),
   pushAt 2824 2 6144,
   opAt 2825 .MSTORE,
   opAt 2826 (.Dup ⟨0, by decide⟩),
   opAt 2827 (.Dup ⟨2, by decide⟩),
   opAt 2828 .DIV,
   opAt 2829 (.Dup ⟨0, by decide⟩),
   pushAt 2830 2 6176,
   opAt 2831 .MSTORE,
   opAt 2832 (.Dup ⟨1, by decide⟩),
   pushAt 2833 0 0,
   opAt 2834 .SUB,
   opAt 2835 (.Dup ⟨2, by decide⟩),
   opAt 2836 (.Swap ⟨0, by decide⟩),
   opAt 2837 .DIV,
   pushAt 2838 1 1,
   opAt 2839 .ADD,
   pushAt 2840 2 6208,
   opAt 2841 .MSTORE,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   pushAt 2843 0 0,
   opAt 2844 .SUB,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 (.Swap ⟨0, by decide⟩),
   opAt 2847 .MOD,
   pushAt 2848 2 6240,
   opAt 2849 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 2850 1 1,
   opAt 2851 (.Dup ⟨0, by decide⟩),
   opAt 2852 (.Dup ⟨2, by decide⟩),
   opAt 2853 .MUL,
   pushAt 2854 1 2,
   opAt 2855 .SUB,
   opAt 2856 .MUL,
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
   opAt 2868 .MUL,
   opAt 2869 (.Dup ⟨0, by decide⟩),
   opAt 2870 (.Dup ⟨2, by decide⟩),
   opAt 2871 .MUL,
   pushAt 2872 1 2,
   opAt 2873 .SUB,
   opAt 2874 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
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
   opAt 2893 (.Dup ⟨0, by decide⟩),
   opAt 2894 (.Dup ⟨2, by decide⟩),
   opAt 2895 .MUL,
   pushAt 2896 1 2,
   opAt 2897 .SUB,
   opAt 2898 .MUL,
   pushAt 2899 2 6272,
   opAt 2900 .MSTORE,
   opAt 2901 .POP,
   opAt 2902 .POP,
   opAt 2903 .POP,
   opAt 2904 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2905 .JUMPDEST,
   opAt 2906 (.Dup ⟨0, by decide⟩),
   opAt 2907 .ISZERO,
   pushAt 2908 2 4426,
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
  [
   pushAt 2918 2 2048,
   opAt 2919 .MLOAD,
   pushAt 2920 2 6144,
   opAt 2921 .MLOAD,
   opAt 2922 (.Dup ⟨1, by decide⟩),
   opAt 2923 (.Dup ⟨1, by decide⟩),
   opAt 2924 (.Swap ⟨0, by decide⟩),
   opAt 2925 .DIV,
   opAt 2926 (.Swap ⟨1, by decide⟩),
   opAt 2927 .MOD,
   pushAt 2928 2 6208,
   opAt 2929 .MLOAD,
   opAt 2930 .MUL,
   pushAt 2931 2 2080,
   opAt 2932 .MLOAD,
   pushAt 2933 2 6144,
   opAt 2934 .MLOAD,
   opAt 2935 (.Swap ⟨0, by decide⟩),
   opAt 2936 .DIV,
   opAt 2937 .ADD,
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
      opAt 2960 .GT,
   opAt 2961 .ISZERO,
   pushAt 2962 0 0,
   opAt 2963 .SUB,
   opAt 2964 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 2965 0 0,
   pushAt 2966 2 9440,
   opAt 2967 .MLOAD,
   pushAt 2968 2 9408,
   opAt 2969 .MLOAD,
   pushAt 2970 2 5120,
   opAt 2971 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2972 .JUMPDEST,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 .MLOAD,
   pushAt 2975 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2976 (.Dup ⟨5, by decide⟩),
   opAt 2977 (.Dup ⟨2, by decide⟩),
   opAt 2978 .MUL,
   opAt 2979 (.Swap ⟨1, by decide⟩),
   opAt 2980 (.Dup ⟨6, by decide⟩),
   opAt 2981 .MULMOD,
   opAt 2982 (.Dup ⟨1, by decide⟩),
   opAt 2983 (.Dup ⟨1, by decide⟩),
   opAt 2984 .LT,
   opAt 2985 .SUB,
   opAt 2986 (.Dup ⟨4, by decide⟩),
   opAt 2987 (.Dup ⟨2, by decide⟩),
   opAt 2988 .ADD,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   opAt 2990 (.Swap ⟨5, by decide⟩),
   opAt 2991 .GT,
   opAt 2992 .SUB,
   opAt 2993 .SUB,
   opAt 2994 (.Dup ⟨3, by decide⟩),
   opAt 2995 (.Dup ⟨3, by decide⟩),
   opAt 2996 .MLOAD,
   opAt 2997 .ADD,
   opAt 2998 (.Dup ⟨0, by decide⟩),
   opAt 2999 (.Swap ⟨4, by decide⟩),
   opAt 3000 .GT,
   opAt 3001 .ADD,
   opAt 3002 (.Swap ⟨2, by decide⟩),
   opAt 3003 (.Dup ⟨2, by decide⟩),
   pushAt 3004 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3005 .ADD,
   opAt 3006 (.Swap ⟨2, by decide⟩),
   opAt 3007 .MSTORE,
   pushAt 3008 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3009 .ADD,
   pushAt 3010 2 8224,
   opAt 3011 (.Dup ⟨2, by decide⟩),
   opAt 3012 .GT,
   pushAt 3013 2 4093,
   opAt 3014 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3015 .POP,
   opAt 3016 .POP,
   pushAt 3017 2 8224,
   opAt 3018 .MLOAD,
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 .ADD,
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 (.Dup ⟨1, by decide⟩),
   opAt 3023 .LT,
   opAt 3024 (.Swap ⟨1, by decide⟩),
   opAt 3025 .POP,
   opAt 3026 (.Dup ⟨2, by decide⟩),
   opAt 3027 (.Dup ⟨1, by decide⟩),
   opAt 3028 .LT,
   opAt 3029 (.Swap ⟨0, by decide⟩),
   opAt 3030 (.Dup ⟨3, by decide⟩),
   opAt 3031 (.Swap ⟨0, by decide⟩),
   opAt 3032 .SUB,
   opAt 3033 (.Dup ⟨0, by decide⟩),
   pushAt 3034 2 8224,
   opAt 3035 .MSTORE,
   opAt 3036 .POP,
   opAt 3037 .GT,
   opAt 3038 (.Swap ⟨0, by decide⟩),
   opAt 3039 .POP,
   opAt 3040 .ISZERO,
   pushAt 3041 2 4337,
   opAt 3042 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3043 .JUMPDEST,
   pushAt 3044 0 0,
   pushAt 3045 2 9440,
   opAt 3046 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3047 .JUMPDEST,
   opAt 3048 (.Dup ⟨0, by decide⟩),
   opAt 3049 .MLOAD,
   opAt 3050 (.Dup ⟨1, by decide⟩),
   pushAt 3051 2 8256,
   opAt 3052 (.Swap ⟨0, by decide⟩),
   opAt 3053 .SUB,
   opAt 3054 .MLOAD,
   opAt 3055 (.Dup ⟨1, by decide⟩),
   opAt 3056 .ADD,
   opAt 3057 (.Dup ⟨0, by decide⟩),
   opAt 3058 (.Dup ⟨2, by decide⟩),
   opAt 3059 .GT,
   opAt 3060 (.Swap ⟨1, by decide⟩),
   opAt 3061 .POP,
   opAt 3062 (.Dup ⟨3, by decide⟩),
   opAt 3063 .ADD,
   opAt 3064 (.Dup ⟨0, by decide⟩),
   opAt 3065 (.Dup ⟨4, by decide⟩),
   opAt 3066 .GT,
   opAt 3067 (.Swap ⟨3, by decide⟩),
   opAt 3068 .POP,
   opAt 3069 (.Dup ⟨2, by decide⟩),
   opAt 3070 .MSTORE,
   opAt 3071 (.Swap ⟨0, by decide⟩),
   opAt 3072 (.Swap ⟨1, by decide⟩),
   opAt 3073 .OR,
   opAt 3074 (.Swap ⟨0, by decide⟩),
   pushAt 3075 1 31, opAt 3076 .NOT,
   opAt 3077 .ADD,
   pushAt 3078 2 8255,
   opAt 3079 (.Dup ⟨1, by decide⟩),
   opAt 3080 .GT,
   pushAt 3081 2 4276,
   opAt 3082 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3083 .POP,
   pushAt 3084 2 8224,
   opAt 3085 .MLOAD,
   opAt 3086 (.Dup ⟨1, by decide⟩),
   opAt 3087 .ADD,
   opAt 3088 (.Dup ⟨0, by decide⟩),
   pushAt 3089 2 8224,
   opAt 3090 .MSTORE,
   opAt 3091 .LT,
   opAt 3092 .ISZERO,
   pushAt 3093 2 4270,
   opAt 3094 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3095 .JUMPDEST,
   pushAt 3096 2 8224,
   opAt 3097 .MLOAD,
   opAt 3098 .ISZERO,
   pushAt 3099 2 4406,
   opAt 3100 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3101 0 0,
   pushAt 3102 2 9440,
   opAt 3103 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3104 .JUMPDEST,
   opAt 3105 (.Dup ⟨0, by decide⟩),
   opAt 3106 .MLOAD,
   opAt 3107 (.Dup ⟨1, by decide⟩),
   pushAt 3108 2 8256,
   opAt 3109 (.Swap ⟨0, by decide⟩),
   opAt 3110 .SUB,
   opAt 3111 .MLOAD,
   opAt 3112 (.Dup ⟨1, by decide⟩),
   opAt 3113 (.Dup ⟨1, by decide⟩),
   opAt 3114 .GT,
   opAt 3115 (.Swap ⟨1, by decide⟩),
   opAt 3116 .SUB,
   opAt 3117 (.Dup ⟨3, by decide⟩),
   opAt 3118 (.Dup ⟨1, by decide⟩),
   opAt 3119 .LT,
   opAt 3120 (.Swap ⟨0, by decide⟩),
   opAt 3121 (.Dup ⟨4, by decide⟩),
   opAt 3122 (.Swap ⟨0, by decide⟩),
   opAt 3123 .SUB,
   opAt 3124 (.Dup ⟨3, by decide⟩),
   opAt 3125 .MSTORE,
   opAt 3126 .OR,
   opAt 3127 (.Swap ⟨1, by decide⟩),
   opAt 3128 .POP,
   pushAt 3129 1 31, opAt 3130 .NOT,
   opAt 3131 .ADD,
   pushAt 3132 2 8255,
   opAt 3133 (.Dup ⟨1, by decide⟩),
   opAt 3134 .GT,
   pushAt 3135 2 4352,
   opAt 3136 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3137 .POP,
   pushAt 3138 2 8224,
   opAt 3139 .MLOAD,
   opAt 3140 .SUB,
   pushAt 3141 2 8224,
   opAt 3142 .MSTORE,
   pushAt 3143 2 4337,
   opAt 3144 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3145 .JUMPDEST,
   pushAt 3146 2 4417,
   pushAt 3147 2 2048,
   pushAt 3148 2 2292,
   opAt 3149 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3150 .JUMPDEST,
   pushAt 3151 1 1,
   opAt 3152 (.Swap ⟨0, by decide⟩),
   opAt 3153 .SUB,
   pushAt 3154 2 3994,
   opAt 3155 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3156 .JUMPDEST,
   opAt 3157 .POP,
   pushAt 3158 2 1748,
   opAt 3159 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3795 = true :=
  Artifact.isValidJumpDest_index 2755 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3839 = true :=
  Artifact.isValidJumpDest_index 2782 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3844 = true :=
  Artifact.isValidJumpDest_index 2785 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3851 = true :=
  Artifact.isValidJumpDest_index 2789 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3882 = true :=
  Artifact.isValidJumpDest_index 2813 (by rfl)



theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3994 = true :=
  Artifact.isValidJumpDest_index 2905 (by rfl)



theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4093 = true :=
  Artifact.isValidJumpDest_index 2972 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4270 = true :=
  Artifact.isValidJumpDest_index 3043 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4276 = true :=
  Artifact.isValidJumpDest_index 3047 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4337 = true :=
  Artifact.isValidJumpDest_index 3095 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4352 = true :=
  Artifact.isValidJumpDest_index 3104 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4406 = true :=
  Artifact.isValidJumpDest_index 3145 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4417 = true :=
  Artifact.isValidJumpDest_index 3150 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4426 = true :=
  Artifact.isValidJumpDest_index 3156 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
