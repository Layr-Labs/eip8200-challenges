import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2862..2873, pc 4643..4657. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2780 .JUMPDEST,
   opAt 2781 (.Dup ⟨0, by decide⟩),
   opAt 2782 (.Dup ⟨3, by decide⟩),
   opAt 2783 .EQ,
   pushAt 2784 0 0,
   opAt 2785 .MLOAD,
   pushAt 2786 1 255,
   opAt 2787 .SHR,
   opAt 2788 .AND,
   opAt 2789 .ISZERO,
   pushAt 2790 2 4687,
   opAt 2791 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2792 (.Dup ⟨0, by decide⟩),
   pushAt 2793 1 96,
   pushAt 2794 2 1024,
   opAt 2795 .CALLDATACOPY,
   opAt 2796 (.Dup ⟨0, by decide⟩),
   pushAt 2797 1 96,
   pushAt 2798 2 8256,
   opAt 2799 .CALLDATACOPY,
   pushAt 2800 0 0,
   pushAt 2801 2 8224,
   opAt 2802 .MSTORE,
   pushAt 2803 2 4692,
   pushAt 2804 2 2048,
   pushAt 2805 2 2642,
   opAt 2806 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2807 .JUMPDEST,
   pushAt 2808 2 1533,
   opAt 2809 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2810 .JUMPDEST,
   pushAt 2811 1 1,
   pushAt 2812 2 9408,
   opAt 2813 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2814 .JUMPDEST,
   opAt 2815 (.Dup ⟨0, by decide⟩),
   opAt 2816 .MLOAD,
   opAt 2817 .NOT,
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .ADD,
   opAt 2820 (.Dup ⟨2, by decide⟩),
   opAt 2821 (.Dup ⟨1, by decide⟩),
   opAt 2822 .LT,
   opAt 2823 (.Swap ⟨2, by decide⟩),
   opAt 2824 .POP,
   opAt 2825 (.Dup ⟨1, by decide⟩),
   pushAt 2826 2 5120,
   opAt 2827 .ADD,
   opAt 2828 .MSTORE,
   opAt 2829 (.Dup ⟨0, by decide⟩),
   opAt 2830 .ISZERO,
   pushAt 2831 2 4760,
   opAt 2832 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2833 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2834 .ADD,
   pushAt 2835 2 4699,
   opAt 2836 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2837 .JUMPDEST,
   opAt 2838 .POP,
   opAt 2839 .POP,
   pushAt 2840 0 0,
   opAt 2841 .MLOAD,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   pushAt 2843 0 0,
   opAt 2844 .SUB,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 .AND,
   opAt 2847 (.Dup ⟨0, by decide⟩),
   pushAt 2848 2 6144,
   opAt 2849 .MSTORE,
   opAt 2850 (.Dup ⟨0, by decide⟩),
   opAt 2851 (.Dup ⟨2, by decide⟩),
   opAt 2852 .DIV,
   opAt 2853 (.Dup ⟨0, by decide⟩),
   pushAt 2854 2 6176,
   opAt 2855 .MSTORE,
   opAt 2856 (.Dup ⟨1, by decide⟩),
   pushAt 2857 0 0,
   opAt 2858 .SUB,
   opAt 2859 (.Dup ⟨2, by decide⟩),
   opAt 2860 (.Swap ⟨0, by decide⟩),
   opAt 2861 .DIV,
   pushAt 2862 1 1,
   opAt 2863 .ADD,
   pushAt 2864 2 6208,
   opAt 2865 .MSTORE,
   opAt 2866 (.Dup ⟨0, by decide⟩),
   pushAt 2867 0 0,
   opAt 2868 .SUB,
   opAt 2869 (.Dup ⟨1, by decide⟩),
   opAt 2870 (.Swap ⟨0, by decide⟩),
   opAt 2871 .MOD,
   pushAt 2872 2 6240,
   opAt 2873 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2874 .JUMPDEST,
   pushAt 2875 1 1,
   opAt 2876 (.Dup ⟨0, by decide⟩),
   opAt 2877 (.Dup ⟨2, by decide⟩),
   opAt 2878 .MUL,
   pushAt 2879 1 2,
   opAt 2880 .SUB,
   opAt 2881 .MUL,
   opAt 2882 (.Dup ⟨0, by decide⟩),
   opAt 2883 (.Dup ⟨2, by decide⟩),
   opAt 2884 .MUL,
   pushAt 2885 1 2,
   opAt 2886 .SUB,
   opAt 2887 .MUL,
   opAt 2888 (.Dup ⟨0, by decide⟩),
   opAt 2889 (.Dup ⟨2, by decide⟩),
   opAt 2890 .MUL,
   pushAt 2891 1 2,
   opAt 2892 .SUB,
   opAt 2893 .MUL,
   opAt 2894 (.Dup ⟨0, by decide⟩),
   opAt 2895 (.Dup ⟨2, by decide⟩),
   opAt 2896 .MUL,
   pushAt 2897 1 2,
   opAt 2898 .SUB,
   opAt 2899 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2900 .JUMPDEST,
   opAt 2901 (.Dup ⟨0, by decide⟩),
   opAt 2902 (.Dup ⟨2, by decide⟩),
   opAt 2903 .MUL,
   pushAt 2904 1 2,
   opAt 2905 .SUB,
   opAt 2906 .MUL,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 (.Dup ⟨2, by decide⟩),
   opAt 2909 .MUL,
   pushAt 2910 1 2,
   opAt 2911 .SUB,
   opAt 2912 .MUL,
   opAt 2913 (.Dup ⟨0, by decide⟩),
   opAt 2914 (.Dup ⟨2, by decide⟩),
   opAt 2915 .MUL,
   pushAt 2916 1 2,
   opAt 2917 .SUB,
   opAt 2918 .MUL,
   opAt 2919 (.Dup ⟨0, by decide⟩),
   opAt 2920 (.Dup ⟨2, by decide⟩),
   opAt 2921 .MUL,
   pushAt 2922 1 2,
   opAt 2923 .SUB,
   opAt 2924 .MUL,
   pushAt 2925 2 6272,
   opAt 2926 .MSTORE,
   opAt 2927 .POP,
   opAt 2928 .POP,
   opAt 2929 .POP,
   opAt 2930 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2931 .JUMPDEST,
   opAt 2932 (.Dup ⟨0, by decide⟩),
   opAt 2933 .ISZERO,
   pushAt 2934 2 5366,
   opAt 2935 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2936 (.Dup ⟨1, by decide⟩),
   pushAt 2937 2 2048,
   pushAt 2938 2 8224,
   opAt 2939 .MCOPY,
   pushAt 2940 0 0,
   pushAt 2941 2 9440,
   opAt 2942 .MLOAD,
   opAt 2943 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2944 .JUMPDEST,
   pushAt 2945 2 2048,
   opAt 2946 .MLOAD,
   pushAt 2947 2 6144,
   opAt 2948 .MLOAD,
   opAt 2949 (.Dup ⟨1, by decide⟩),
   opAt 2950 (.Dup ⟨1, by decide⟩),
   opAt 2951 (.Swap ⟨0, by decide⟩),
   opAt 2952 .DIV,
   opAt 2953 (.Swap ⟨1, by decide⟩),
   opAt 2954 .MOD,
   pushAt 2955 2 6208,
   opAt 2956 .MLOAD,
   opAt 2957 .MUL,
   pushAt 2958 2 2080,
   opAt 2959 .MLOAD,
   pushAt 2960 2 6144,
   opAt 2961 .MLOAD,
   opAt 2962 (.Swap ⟨0, by decide⟩),
   opAt 2963 .DIV,
   opAt 2964 .ADD,
   pushAt 2965 2 6176,
   opAt 2966 .MLOAD,
   opAt 2967 (.Dup ⟨0, by decide⟩),
   pushAt 2968 2 6240,
   opAt 2969 .MLOAD,
   opAt 2970 (.Dup ⟨4, by decide⟩),
   opAt 2971 .MULMOD,
   opAt 2972 (.Dup ⟨2, by decide⟩),
   opAt 2973 (.Swap ⟨0, by decide⟩),
   opAt 2974 .ADDMOD,
   opAt 2975 (.Swap ⟨0, by decide⟩),
   opAt 2976 .SUB,
   pushAt 2977 2 6272,
   opAt 2978 .MLOAD,
   opAt 2979 .MUL,
   opAt 2980 (.Dup ⟨0, by decide⟩),
   opAt 2981 .ISZERO,
   opAt 2982 .ISZERO,
   opAt 2983 (.Swap ⟨0, by decide⟩),
   opAt 2984 .SUB,
   opAt 2985 (.Swap ⟨0, by decide⟩),
   opAt 2986 .POP]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2987 .JUMPDEST,
   pushAt 2988 0 0,
   pushAt 2989 2 9440,
   opAt 2990 .MLOAD,
   pushAt 2991 2 9408,
   opAt 2992 .MLOAD,
   pushAt 2993 2 5120,
   opAt 2994 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2995 .JUMPDEST,
   opAt 2996 (.Dup ⟨3, by decide⟩),
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 (.Dup ⟨1, by decide⟩),
   opAt 3000 (.Dup ⟨1, by decide⟩),
   opAt 3001 .MUL,
   opAt 3002 (.Swap ⟨1, by decide⟩),
   pushAt 3003 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3004 (.Swap ⟨1, by decide⟩),
   opAt 3005 .MULMOD,
   opAt 3006 (.Dup ⟨1, by decide⟩),
   opAt 3007 (.Dup ⟨1, by decide⟩),
   opAt 3008 .LT,
   opAt 3009 (.Dup ⟨2, by decide⟩),
   opAt 3010 .ADD,
   opAt 3011 (.Swap ⟨0, by decide⟩),
   opAt 3012 .SUB,
   opAt 3013 (.Dup ⟨3, by decide⟩),
   opAt 3014 .MLOAD,
   opAt 3015 (.Swap ⟨1, by decide⟩),
   opAt 3016 (.Dup ⟨2, by decide⟩),
   opAt 3017 .ADD,
   opAt 3018 (.Swap ⟨1, by decide⟩),
   opAt 3019 (.Dup ⟨2, by decide⟩),
   opAt 3020 .LT,
   opAt 3021 .ADD,
   opAt 3022 (.Swap ⟨0, by decide⟩),
   opAt 3023 (.Dup ⟨4, by decide⟩),
   opAt 3024 .ADD,
   opAt 3025 (.Swap ⟨3, by decide⟩),
   opAt 3026 (.Dup ⟨4, by decide⟩),
   opAt 3027 .LT,
   opAt 3028 .ADD,
   opAt 3029 (.Swap ⟨2, by decide⟩),
   opAt 3030 (.Dup ⟨2, by decide⟩),
   opAt 3031 .MSTORE,
   pushAt 3032 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3033 .ADD,
   opAt 3034 (.Swap ⟨0, by decide⟩),
   pushAt 3035 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3036 .ADD,
   opAt 3037 (.Swap ⟨0, by decide⟩),
   pushAt 3038 2 8224,
   opAt 3039 (.Dup ⟨2, by decide⟩),
   opAt 3040 .GT,
   pushAt 3041 2 4968,
   opAt 3042 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3043 .POP,
   opAt 3044 .POP,
   pushAt 3045 2 8224,
   opAt 3046 .MLOAD,
   opAt 3047 (.Dup ⟨1, by decide⟩),
   opAt 3048 .ADD,
   opAt 3049 (.Dup ⟨1, by decide⟩),
   opAt 3050 (.Dup ⟨1, by decide⟩),
   opAt 3051 .LT,
   opAt 3052 (.Swap ⟨1, by decide⟩),
   opAt 3053 .POP,
   opAt 3054 (.Dup ⟨2, by decide⟩),
   opAt 3055 (.Dup ⟨1, by decide⟩),
   opAt 3056 .LT,
   opAt 3057 (.Swap ⟨0, by decide⟩),
   opAt 3058 (.Dup ⟨3, by decide⟩),
   opAt 3059 (.Swap ⟨0, by decide⟩),
   opAt 3060 .SUB,
   opAt 3061 (.Dup ⟨0, by decide⟩),
   pushAt 3062 2 8224,
   opAt 3063 .MSTORE,
   opAt 3064 .POP,
   opAt 3065 .GT,
   opAt 3066 (.Swap ⟨0, by decide⟩),
   opAt 3067 .POP,
   opAt 3068 .ISZERO,
   pushAt 3069 2 5247,
   opAt 3070 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3071 .JUMPDEST,
   pushAt 3072 0 0,
   pushAt 3073 2 9440,
   opAt 3074 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3075 .JUMPDEST,
   opAt 3076 (.Dup ⟨0, by decide⟩),
   opAt 3077 .MLOAD,
   opAt 3078 (.Dup ⟨1, by decide⟩),
   pushAt 3079 2 8256,
   opAt 3080 (.Swap ⟨0, by decide⟩),
   opAt 3081 .SUB,
   opAt 3082 .MLOAD,
   opAt 3083 (.Dup ⟨1, by decide⟩),
   opAt 3084 .ADD,
   opAt 3085 (.Dup ⟨0, by decide⟩),
   opAt 3086 (.Dup ⟨2, by decide⟩),
   opAt 3087 .GT,
   opAt 3088 (.Swap ⟨1, by decide⟩),
   opAt 3089 .POP,
   opAt 3090 (.Dup ⟨3, by decide⟩),
   opAt 3091 .ADD,
   opAt 3092 (.Dup ⟨0, by decide⟩),
   opAt 3093 (.Dup ⟨4, by decide⟩),
   opAt 3094 .GT,
   opAt 3095 (.Swap ⟨3, by decide⟩),
   opAt 3096 .POP,
   opAt 3097 (.Dup ⟨2, by decide⟩),
   opAt 3098 .MSTORE,
   opAt 3099 (.Swap ⟨0, by decide⟩),
   opAt 3100 (.Swap ⟨1, by decide⟩),
   opAt 3101 .OR,
   opAt 3102 (.Swap ⟨0, by decide⟩),
   pushAt 3103 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3104 .ADD,
   pushAt 3105 2 8255,
   opAt 3106 (.Dup ⟨1, by decide⟩),
   opAt 3107 .GT,
   pushAt 3108 2 5156,
   opAt 3109 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 .POP,
   pushAt 3111 2 8224,
   opAt 3112 .MLOAD,
   opAt 3113 (.Dup ⟨1, by decide⟩),
   opAt 3114 .ADD,
   opAt 3115 (.Dup ⟨0, by decide⟩),
   pushAt 3116 2 8224,
   opAt 3117 .MSTORE,
   opAt 3118 .LT,
   opAt 3119 .ISZERO,
   pushAt 3120 2 5150,
   opAt 3121 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3122 .JUMPDEST,
   pushAt 3123 2 8224,
   opAt 3124 .MLOAD,
   opAt 3125 .ISZERO,
   pushAt 3126 2 5346,
   opAt 3127 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3128 0 0,
   pushAt 3129 2 9440,
   opAt 3130 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3131 .JUMPDEST,
   opAt 3132 (.Dup ⟨0, by decide⟩),
   opAt 3133 .MLOAD,
   opAt 3134 (.Dup ⟨1, by decide⟩),
   pushAt 3135 2 8256,
   opAt 3136 (.Swap ⟨0, by decide⟩),
   opAt 3137 .SUB,
   opAt 3138 .MLOAD,
   opAt 3139 (.Dup ⟨1, by decide⟩),
   opAt 3140 (.Dup ⟨1, by decide⟩),
   opAt 3141 .GT,
   opAt 3142 (.Swap ⟨1, by decide⟩),
   opAt 3143 .SUB,
   opAt 3144 (.Dup ⟨3, by decide⟩),
   opAt 3145 (.Dup ⟨1, by decide⟩),
   opAt 3146 .LT,
   opAt 3147 (.Swap ⟨0, by decide⟩),
   opAt 3148 (.Dup ⟨4, by decide⟩),
   opAt 3149 (.Swap ⟨0, by decide⟩),
   opAt 3150 .SUB,
   opAt 3151 (.Dup ⟨3, by decide⟩),
   opAt 3152 .MSTORE,
   opAt 3153 .OR,
   opAt 3154 (.Swap ⟨1, by decide⟩),
   opAt 3155 .POP,
   pushAt 3156 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3157 .ADD,
   pushAt 3158 2 8255,
   opAt 3159 (.Dup ⟨1, by decide⟩),
   opAt 3160 .GT,
   pushAt 3161 2 5262,
   opAt 3162 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3163 .POP,
   pushAt 3164 2 8224,
   opAt 3165 .MLOAD,
   opAt 3166 .SUB,
   pushAt 3167 2 8224,
   opAt 3168 .MSTORE,
   pushAt 3169 2 5247,
   opAt 3170 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3171 .JUMPDEST,
   pushAt 3172 2 5357,
   pushAt 3173 2 2048,
   pushAt 3174 2 2642,
   opAt 3175 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3176 .JUMPDEST,
   pushAt 3177 1 1,
   opAt 3178 (.Swap ⟨0, by decide⟩),
   opAt 3179 .SUB,
   pushAt 3180 2 4874,
   opAt 3181 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3182 .JUMPDEST,
   opAt 3183 .POP,
   pushAt 3184 2 1756,
   opAt 3185 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4643 = true :=
  Artifact.isValidJumpDest_index 2780 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4687 = true :=
  Artifact.isValidJumpDest_index 2807 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4692 = true :=
  Artifact.isValidJumpDest_index 2810 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4699 = true :=
  Artifact.isValidJumpDest_index 2814 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4760 = true :=
  Artifact.isValidJumpDest_index 2837 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4806 = true :=
  Artifact.isValidJumpDest_index 2874 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4837 = true :=
  Artifact.isValidJumpDest_index 2900 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4874 = true :=
  Artifact.isValidJumpDest_index 2931 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4895 = true :=
  Artifact.isValidJumpDest_index 2944 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4954 = true :=
  Artifact.isValidJumpDest_index 2987 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4968 = true :=
  Artifact.isValidJumpDest_index 2995 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5150 = true :=
  Artifact.isValidJumpDest_index 3071 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5156 = true :=
  Artifact.isValidJumpDest_index 3075 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5247 = true :=
  Artifact.isValidJumpDest_index 3122 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5262 = true :=
  Artifact.isValidJumpDest_index 3131 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5346 = true :=
  Artifact.isValidJumpDest_index 3171 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5357 = true :=
  Artifact.isValidJumpDest_index 3176 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5366 = true :=
  Artifact.isValidJumpDest_index 3182 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
