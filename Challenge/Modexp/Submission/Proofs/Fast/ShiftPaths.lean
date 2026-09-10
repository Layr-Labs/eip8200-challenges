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
  [opAt 2725 .JUMPDEST,
   opAt 2726 (.Dup ⟨0, by decide⟩),
   opAt 2727 (.Dup ⟨3, by decide⟩),
   opAt 2728 .EQ,
   pushAt 2729 0 0,
   opAt 2730 .MLOAD,
   pushAt 2731 1 255,
   opAt 2732 .SHR,
   opAt 2733 .AND,
   opAt 2734 .ISZERO,
   pushAt 2735 2 3824,
   opAt 2736 .JUMPI]

/-- Instructions 2874..2526, pc 3856..3884. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2737 (.Dup ⟨0, by decide⟩),
   pushAt 2738 1 96,
   pushAt 2739 2 1024,
   opAt 2740 .CALLDATACOPY,
   opAt 2741 (.Dup ⟨0, by decide⟩),
   pushAt 2742 1 96,
   pushAt 2743 2 8256,
   opAt 2744 .CALLDATACOPY,
   pushAt 2745 0 0,
   pushAt 2746 2 8224,
   opAt 2747 .MSTORE,
   pushAt 2748 2 3829,
   pushAt 2749 2 2048,
   pushAt 2750 2 2282,
   opAt 2751 .JUMP]

/-- Instructions 2889..2891, pc 4390..3889. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2752 .JUMPDEST,
   pushAt 2753 2 1517,
   opAt 2754 .JUMP]

/-- Instructions 2530..2533, pc 3890..4401. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2755 .JUMPDEST,
   pushAt 2756 1 1,
   pushAt 2757 2 9408,
   opAt 2758 .MLOAD]

/-- Instructions 2534..2914, pc 4402..4977. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2759 .JUMPDEST,
   opAt 2760 (.Dup ⟨0, by decide⟩),
   opAt 2761 .MLOAD,
   opAt 2762 .NOT,
   opAt 2763 (.Dup ⟨2, by decide⟩),
   opAt 2764 .ADD,
   opAt 2765 (.Dup ⟨2, by decide⟩),
   opAt 2766 (.Dup ⟨1, by decide⟩),
   opAt 2767 .LT,
   opAt 2768 (.Swap ⟨2, by decide⟩),
   opAt 2769 .POP,
   opAt 2770 (.Dup ⟨1, by decide⟩),
   pushAt 2771 2 5120,
   opAt 2772 .ADD,
   opAt 2773 .MSTORE,
   opAt 2774 (.Dup ⟨0, by decide⟩),
   opAt 2775 .ISZERO,
   pushAt 2776 2 3867,
   opAt 2777 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3927. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2778 1 31,
   opAt 2779 .NOT,
   opAt 2780 .ADD,
   pushAt 2781 2 3836,
   opAt 2782 .JUMP]

/-- Instructions 2557..2593, pc 3928..3973. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2783 .JUMPDEST,
   opAt 2784 .POP,
   opAt 2785 .POP,
   pushAt 2786 0 0,
   opAt 2787 .MLOAD,
   opAt 2788 (.Dup ⟨0, by decide⟩),
   pushAt 2789 0 0,
   opAt 2790 .SUB,
   opAt 2791 (.Dup ⟨1, by decide⟩),
   opAt 2792 .AND,
   opAt 2793 (.Dup ⟨0, by decide⟩),
   pushAt 2794 2 6144,
   opAt 2795 .MSTORE,
   opAt 2796 (.Dup ⟨0, by decide⟩),
   opAt 2797 (.Dup ⟨2, by decide⟩),
   opAt 2798 .DIV,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   pushAt 2800 2 6176,
   opAt 2801 .MSTORE,
   opAt 2802 (.Dup ⟨1, by decide⟩),
   pushAt 2803 0 0,
   opAt 2804 .SUB,
   opAt 2805 (.Dup ⟨2, by decide⟩),
   opAt 2806 (.Swap ⟨0, by decide⟩),
   opAt 2807 .DIV,
   pushAt 2808 1 1,
   opAt 2809 .ADD,
   pushAt 2810 2 6208,
   opAt 2811 .MSTORE,
   opAt 2812 (.Dup ⟨0, by decide⟩),
   pushAt 2813 0 0,
   opAt 2814 .SUB,
   opAt 2815 (.Dup ⟨1, by decide⟩),
   opAt 2816 (.Swap ⟨0, by decide⟩),
   opAt 2817 .MOD,
   pushAt 2818 2 6240,
   opAt 2819 .MSTORE]

/-- Instructions 2594..2981, pc 3974..4004. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2820 (.Dup ⟨0, by decide⟩),
   pushAt 2821 1 3,
   opAt 2822 .MUL,
   pushAt 2823 1 2,
   opAt 2824 .XOR,
   opAt 2825 (.Dup ⟨0, by decide⟩),
   opAt 2826 (.Dup ⟨2, by decide⟩),
   opAt 2827 .MUL,
   pushAt 2828 1 2,
   opAt 2829 .SUB,
   opAt 2830 .MUL,
   opAt 2831 (.Dup ⟨0, by decide⟩),
   opAt 2832 (.Dup ⟨2, by decide⟩),
   opAt 2833 .MUL,
   pushAt 2834 1 2,
   opAt 2835 .SUB,
   opAt 2836 .MUL]

/-- Instructions 2620..3012, pc 4005..5129. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2837 (.Dup ⟨0, by decide⟩),
   opAt 2838 (.Dup ⟨2, by decide⟩),
   opAt 2839 .MUL,
   pushAt 2840 1 2,
   opAt 2841 .SUB,
   opAt 2842 .MUL,
   opAt 2843 (.Dup ⟨0, by decide⟩),
   opAt 2844 (.Dup ⟨2, by decide⟩),
   opAt 2845 .MUL,
   pushAt 2846 1 2,
   opAt 2847 .SUB,
   opAt 2848 .MUL,
   opAt 2849 (.Dup ⟨0, by decide⟩),
   opAt 2850 (.Dup ⟨2, by decide⟩),
   opAt 2851 .MUL,
   pushAt 2852 1 2,
   opAt 2853 .SUB,
   opAt 2854 .MUL,
   opAt 2855 (.Dup ⟨0, by decide⟩),
   opAt 2856 (.Dup ⟨2, by decide⟩),
   opAt 2857 .MUL,
   pushAt 2858 1 2,
   opAt 2859 .SUB,
   opAt 2860 .MUL,
   pushAt 2861 2 6272,
   opAt 2862 .MSTORE,
   opAt 2863 .POP,
   opAt 2864 .POP,
   opAt 2865 .POP,
   pushAt 2866 1 32,
   opAt 2867 .MLOAD,
   pushAt 2868 1 128,
   opAt 2869 .SHR,
   pushAt 2870 2 6304,
   opAt 2871 .MSTORE,
   opAt 2872 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4042..4048. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2873 .JUMPDEST,
   opAt 2874 (.Dup ⟨0, by decide⟩),
   opAt 2875 .ISZERO,
   pushAt 2876 2 4422,
   opAt 2877 .JUMPI]

/-- Instructions 2656..2663, pc 4049..4062. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2878 (.Dup ⟨1, by decide⟩),
   pushAt 2879 2 2048,
   pushAt 2880 2 8224,
   opAt 2881 .MCOPY,
   pushAt 2882 0 0,
   pushAt 2883 2 9440,
   opAt 2884 .MLOAD,
   opAt 2885 .MSTORE]

/-- Instructions 3026..2706, pc 5151..4120. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2886 2 2048,
   opAt 2887 .MLOAD,
   pushAt 2888 2 6144,
   opAt 2889 .MLOAD,
   opAt 2890 (.Dup ⟨1, by decide⟩),
   pushAt 2891 2 6208,
   opAt 2892 .MLOAD,
   opAt 2893 .MUL,
   opAt 2894 (.Dup ⟨1, by decide⟩),
   pushAt 2895 2 2080,
   opAt 2896 .MLOAD,
   opAt 2897 .DIV,
   opAt 2898 .ADD,
   opAt 2899 (.Swap ⟨1, by decide⟩),
   opAt 2900 .DIV,
   opAt 2901 (.Swap ⟨0, by decide⟩),
   pushAt 2902 2 6176,
   opAt 2903 .MLOAD,
   opAt 2904 (.Dup ⟨0, by decide⟩),
   pushAt 2905 2 6240,
   opAt 2906 .MLOAD,
   opAt 2907 (.Dup ⟨4, by decide⟩),
   opAt 2908 .MULMOD,
   opAt 2909 (.Dup ⟨2, by decide⟩),
   opAt 2910 .ADDMOD,
   opAt 2911 (.Swap ⟨0, by decide⟩),
   opAt 2912 .SUB,
   pushAt 2913 2 6272,
   opAt 2914 .MLOAD,
   opAt 2915 .MUL,
   opAt 2916 (.Dup ⟨0, by decide⟩),
   pushAt 2917 0 0,
   opAt 2918 .MLOAD,
   opAt 2919 .MUL,
   pushAt 2920 2 2080,
   opAt 2921 .MLOAD,
   opAt 2922 .SUB,
   pushAt 2923 2 6304,
   opAt 2924 .MLOAD,
   opAt 2925 (.Dup ⟨2, by decide⟩),
   pushAt 2926 1 128,
   opAt 2927 .SHR,
   opAt 2928 .MUL,
   opAt 2929 .GT,
   opAt 2930 (.Swap ⟨0, by decide⟩),
   opAt 2931 .SUB,
   opAt 2932 (.Swap ⟨0, by decide⟩),
   pushAt 2933 2 6176,
   opAt 2934 .MLOAD,
   opAt 2935 .GT,
   opAt 2936 .ISZERO,
   pushAt 2937 0 0,
   opAt 2938 .SUB,
   opAt 2939 .OR]

/-- Instructions 2707..3076, pc 4121..5223. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2940 0 0,
   pushAt 2941 2 9440,
   opAt 2942 .MLOAD,
   pushAt 2943 2 9408,
   opAt 2944 .MLOAD,
   pushAt 2945 2 5120,
   opAt 2946 .ADD]

/-- Instructions 2715..2762, pc 5224..4282. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2947 .JUMPDEST,
   opAt 2948 (.Dup ⟨0, by decide⟩),
   opAt 2949 .MLOAD,
   pushAt 2950 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2951 (.Dup ⟨5, by decide⟩),
   opAt 2952 (.Dup ⟨2, by decide⟩),
   opAt 2953 .MUL,
   opAt 2954 (.Swap ⟨1, by decide⟩),
   opAt 2955 (.Dup ⟨6, by decide⟩),
   opAt 2956 .MULMOD,
   opAt 2957 (.Dup ⟨1, by decide⟩),
   opAt 2958 (.Dup ⟨1, by decide⟩),
   opAt 2959 .LT,
   opAt 2960 .SUB,
   opAt 2961 (.Dup ⟨4, by decide⟩),
   opAt 2962 (.Dup ⟨2, by decide⟩),
   opAt 2963 .ADD,
   opAt 2964 (.Dup ⟨0, by decide⟩),
   opAt 2965 (.Swap ⟨5, by decide⟩),
   opAt 2966 .GT,
   opAt 2967 .SUB,
   opAt 2968 .SUB,
   opAt 2969 (.Dup ⟨3, by decide⟩),
   opAt 2970 (.Dup ⟨3, by decide⟩),
   opAt 2971 .MLOAD,
   opAt 2972 .ADD,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 (.Swap ⟨4, by decide⟩),
   opAt 2975 .GT,
   opAt 2976 .ADD,
   opAt 2977 (.Swap ⟨2, by decide⟩),
   opAt 2978 (.Dup ⟨2, by decide⟩),
   pushAt 2979 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2980 .ADD,
   opAt 2981 (.Swap ⟨2, by decide⟩),
   opAt 2982 .MSTORE,
   pushAt 2983 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2984 .ADD,
   pushAt 2985 2 8224,
   opAt 2986 (.Dup ⟨2, by decide⟩),
   opAt 2987 .GT,
   pushAt 2988 2 4089,
   opAt 2989 .JUMPI]

/-- Instructions 2763..2790, pc 4283..4316. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2990 .POP,
   opAt 2991 .POP,
   pushAt 2992 2 8224,
   opAt 2993 .MLOAD,
   opAt 2994 (.Dup ⟨1, by decide⟩),
   opAt 2995 .ADD,
   opAt 2996 (.Dup ⟨1, by decide⟩),
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 .LT,
   opAt 2999 (.Swap ⟨1, by decide⟩),
   opAt 3000 .POP,
   opAt 3001 (.Dup ⟨2, by decide⟩),
   opAt 3002 (.Dup ⟨1, by decide⟩),
   opAt 3003 .LT,
   opAt 3004 (.Swap ⟨0, by decide⟩),
   opAt 3005 (.Dup ⟨3, by decide⟩),
   opAt 3006 (.Swap ⟨0, by decide⟩),
   opAt 3007 .SUB,
   opAt 3008 (.Dup ⟨0, by decide⟩),
   pushAt 3009 2 8224,
   opAt 3010 .MSTORE,
   opAt 3011 .POP,
   opAt 3012 .GT,
   opAt 3013 (.Swap ⟨0, by decide⟩),
   opAt 3014 .POP,
   opAt 3015 .ISZERO,
   pushAt 3016 2 4333,
   opAt 3017 .JUMPI]

/-- Instructions 2791..2794, pc 4317..4322. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3018 .JUMPDEST,
   pushAt 3019 0 0,
   pushAt 3020 2 9440,
   opAt 3021 .MLOAD]

/-- Instructions 2795..3447, pc 4323..5172. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3022 .JUMPDEST,
   opAt 3023 (.Dup ⟨0, by decide⟩),
   opAt 3024 .MLOAD,
   opAt 3025 (.Dup ⟨1, by decide⟩),
   pushAt 3026 2 8256,
   opAt 3027 (.Swap ⟨0, by decide⟩),
   opAt 3028 .SUB,
   opAt 3029 .MLOAD,
   opAt 3030 (.Dup ⟨1, by decide⟩),
   opAt 3031 .ADD,
   opAt 3032 (.Dup ⟨0, by decide⟩),
   opAt 3033 (.Dup ⟨2, by decide⟩),
   opAt 3034 .GT,
   opAt 3035 (.Swap ⟨1, by decide⟩),
   opAt 3036 .POP,
   opAt 3037 (.Dup ⟨3, by decide⟩),
   opAt 3038 .ADD,
   opAt 3039 (.Dup ⟨0, by decide⟩),
   opAt 3040 (.Dup ⟨4, by decide⟩),
   opAt 3041 .GT,
   opAt 3042 (.Swap ⟨3, by decide⟩),
   opAt 3043 .POP,
   opAt 3044 (.Dup ⟨2, by decide⟩),
   opAt 3045 .MSTORE,
   opAt 3046 (.Swap ⟨0, by decide⟩),
   opAt 3047 (.Swap ⟨1, by decide⟩),
   opAt 3048 .OR,
   opAt 3049 (.Swap ⟨0, by decide⟩),
   pushAt 3050 1 31,
   opAt 3051 .NOT,
   opAt 3052 .ADD,
   pushAt 3053 2 8255,
   opAt 3054 (.Dup ⟨1, by decide⟩),
   opAt 3055 .GT,
   pushAt 3056 2 4272,
   opAt 3057 .JUMPI]

/-- Instructions 2830..2841, pc 4917..5221. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3058 .POP,
   pushAt 3059 2 8224,
   opAt 3060 .MLOAD,
   opAt 3061 (.Dup ⟨1, by decide⟩),
   opAt 3062 .ADD,
   opAt 3063 (.Dup ⟨0, by decide⟩),
   pushAt 3064 2 8224,
   opAt 3065 .MSTORE,
   opAt 3066 .LT,
   opAt 3067 .ISZERO,
   pushAt 3068 2 4266,
   opAt 3069 .JUMPI]

/-- Instructions 2842..2847, pc 5222..4393. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3070 .JUMPDEST,
   pushAt 3071 2 8224,
   opAt 3072 .MLOAD,
   opAt 3073 .ISZERO,
   pushAt 3074 2 4402,
   opAt 3075 .JUMPI]

/-- Instructions 2848..2850, pc 4394..4398. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3076 0 0,
   pushAt 3077 2 9440,
   opAt 3078 .MLOAD]

/-- Instructions 2851..2866, pc 4399..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3079 .JUMPDEST,
   opAt 3080 (.Dup ⟨0, by decide⟩),
   opAt 3081 .MLOAD,
   opAt 3082 (.Dup ⟨1, by decide⟩),
   pushAt 3083 2 8256,
   opAt 3084 (.Swap ⟨0, by decide⟩),
   opAt 3085 .SUB,
   opAt 3086 .MLOAD,
   opAt 3087 (.Dup ⟨1, by decide⟩),
   opAt 3088 (.Dup ⟨1, by decide⟩),
   opAt 3089 .GT,
   opAt 3090 (.Swap ⟨1, by decide⟩),
   opAt 3091 .SUB,
   opAt 3092 (.Dup ⟨3, by decide⟩),
   opAt 3093 (.Dup ⟨1, by decide⟩),
   opAt 3094 .LT,
   opAt 3095 (.Swap ⟨0, by decide⟩),
   opAt 3096 (.Dup ⟨4, by decide⟩),
   opAt 3097 (.Swap ⟨0, by decide⟩),
   opAt 3098 .SUB,
   opAt 3099 (.Dup ⟨3, by decide⟩),
   opAt 3100 .MSTORE,
   opAt 3101 .OR,
   opAt 3102 (.Swap ⟨1, by decide⟩),
   opAt 3103 .POP,
   pushAt 3104 1 31,
   opAt 3105 .NOT,
   opAt 3106 .ADD,
   pushAt 3107 2 8255,
   opAt 3108 (.Dup ⟨1, by decide⟩),
   opAt 3109 .GT,
   pushAt 3110 2 4348,
   opAt 3111 .JUMPI]

/-- Instructions 2867..2874, pc 4439..4452. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3112 .POP,
   pushAt 3113 2 8224,
   opAt 3114 .MLOAD,
   opAt 3115 .SUB,
   pushAt 3116 2 8224,
   opAt 3117 .MSTORE,
   pushAt 3118 2 4333,
   opAt 3119 .JUMP]

/-- Instructions 2875..2879, pc 4453..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3120 .JUMPDEST,
   pushAt 3121 2 4413,
   pushAt 3122 2 2048,
   pushAt 3123 2 2282,
   opAt 3124 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3125 .JUMPDEST,
   pushAt 3126 1 1,
   opAt 3127 (.Swap ⟨0, by decide⟩),
   opAt 3128 .SUB,
   pushAt 3129 2 3980,
   opAt 3130 .JUMP]

/-- Instructions 2886..3523, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3131 .JUMPDEST,
   opAt 3132 .POP,
   pushAt 3133 2 1738,
   opAt 3134 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3780 = true :=
  Artifact.isValidJumpDest_index 2725 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3824 = true :=
  Artifact.isValidJumpDest_index 2752 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3829 = true :=
  Artifact.isValidJumpDest_index 2755 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3836 = true :=
  Artifact.isValidJumpDest_index 2759 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3867 = true :=
  Artifact.isValidJumpDest_index 2783 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3980 = true :=
  Artifact.isValidJumpDest_index 2873 (by rfl)


theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4089 = true :=
  Artifact.isValidJumpDest_index 2947 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4266 = true :=
  Artifact.isValidJumpDest_index 3018 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4272 = true :=
  Artifact.isValidJumpDest_index 3022 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4333 = true :=
  Artifact.isValidJumpDest_index 3070 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4348 = true :=
  Artifact.isValidJumpDest_index 3079 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4402 = true :=
  Artifact.isValidJumpDest_index 3120 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4413 = true :=
  Artifact.isValidJumpDest_index 3125 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4422 = true :=
  Artifact.isValidJumpDest_index 3131 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
