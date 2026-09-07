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
  [opAt 2775 .JUMPDEST,
   opAt 2776 (.Dup ⟨0, by decide⟩),
   opAt 2777 (.Dup ⟨3, by decide⟩),
   opAt 2778 .EQ,
   pushAt 2779 0 0,
   opAt 2780 .MLOAD,
   pushAt 2781 1 255,
   opAt 2782 .SHR,
   opAt 2783 .AND,
   opAt 2784 .ISZERO,
   pushAt 2785 2 4687,
   opAt 2786 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2787 (.Dup ⟨0, by decide⟩),
   pushAt 2788 1 96,
   pushAt 2789 2 1024,
   opAt 2790 .CALLDATACOPY,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   pushAt 2792 1 96,
   pushAt 2793 2 8256,
   opAt 2794 .CALLDATACOPY,
   pushAt 2795 0 0,
   pushAt 2796 2 8224,
   opAt 2797 .MSTORE,
   pushAt 2798 2 4692,
   pushAt 2799 2 2048,
   pushAt 2800 2 2642,
   opAt 2801 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2802 .JUMPDEST,
   pushAt 2803 2 1533,
   opAt 2804 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2805 .JUMPDEST,
   pushAt 2806 1 1,
   pushAt 2807 2 9408,
   opAt 2808 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2809 .JUMPDEST,
   opAt 2810 (.Dup ⟨0, by decide⟩),
   opAt 2811 .MLOAD,
   opAt 2812 .NOT,
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 .ADD,
   opAt 2815 (.Dup ⟨2, by decide⟩),
   opAt 2816 (.Dup ⟨1, by decide⟩),
   opAt 2817 .LT,
   opAt 2818 (.Swap ⟨2, by decide⟩),
   opAt 2819 .POP,
   opAt 2820 (.Dup ⟨1, by decide⟩),
   pushAt 2821 2 5120,
   opAt 2822 .ADD,
   opAt 2823 .MSTORE,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   opAt 2825 .ISZERO,
   pushAt 2826 2 4760,
   opAt 2827 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2828 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2829 .ADD,
   pushAt 2830 2 4699,
   opAt 2831 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2832 .JUMPDEST,
   opAt 2833 .POP,
   opAt 2834 .POP,
   pushAt 2835 0 0,
   opAt 2836 .MLOAD,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   pushAt 2838 0 0,
   opAt 2839 .SUB,
   opAt 2840 (.Dup ⟨1, by decide⟩),
   opAt 2841 .AND,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   pushAt 2843 2 6144,
   opAt 2844 .MSTORE,
   opAt 2845 (.Dup ⟨0, by decide⟩),
   opAt 2846 (.Dup ⟨2, by decide⟩),
   opAt 2847 .DIV,
   opAt 2848 (.Dup ⟨0, by decide⟩),
   pushAt 2849 2 6176,
   opAt 2850 .MSTORE,
   opAt 2851 (.Dup ⟨1, by decide⟩),
   pushAt 2852 0 0,
   opAt 2853 .SUB,
   opAt 2854 (.Dup ⟨2, by decide⟩),
   opAt 2855 (.Swap ⟨0, by decide⟩),
   opAt 2856 .DIV,
   pushAt 2857 1 1,
   opAt 2858 .ADD,
   pushAt 2859 2 6208,
   opAt 2860 .MSTORE,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   pushAt 2862 0 0,
   opAt 2863 .SUB,
   opAt 2864 (.Dup ⟨1, by decide⟩),
   opAt 2865 (.Swap ⟨0, by decide⟩),
   opAt 2866 .MOD,
   pushAt 2867 2 6240,
   opAt 2868 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2869 .JUMPDEST,
   pushAt 2870 1 1,
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
   opAt 2882 .MUL,
   opAt 2883 (.Dup ⟨0, by decide⟩),
   opAt 2884 (.Dup ⟨2, by decide⟩),
   opAt 2885 .MUL,
   pushAt 2886 1 2,
   opAt 2887 .SUB,
   opAt 2888 .MUL,
   opAt 2889 (.Dup ⟨0, by decide⟩),
   opAt 2890 (.Dup ⟨2, by decide⟩),
   opAt 2891 .MUL,
   pushAt 2892 1 2,
   opAt 2893 .SUB,
   opAt 2894 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2895 .JUMPDEST,
   opAt 2896 (.Dup ⟨0, by decide⟩),
   opAt 2897 (.Dup ⟨2, by decide⟩),
   opAt 2898 .MUL,
   pushAt 2899 1 2,
   opAt 2900 .SUB,
   opAt 2901 .MUL,
   opAt 2902 (.Dup ⟨0, by decide⟩),
   opAt 2903 (.Dup ⟨2, by decide⟩),
   opAt 2904 .MUL,
   pushAt 2905 1 2,
   opAt 2906 .SUB,
   opAt 2907 .MUL,
   opAt 2908 (.Dup ⟨0, by decide⟩),
   opAt 2909 (.Dup ⟨2, by decide⟩),
   opAt 2910 .MUL,
   pushAt 2911 1 2,
   opAt 2912 .SUB,
   opAt 2913 .MUL,
   opAt 2914 (.Dup ⟨0, by decide⟩),
   opAt 2915 (.Dup ⟨2, by decide⟩),
   opAt 2916 .MUL,
   pushAt 2917 1 2,
   opAt 2918 .SUB,
   opAt 2919 .MUL,
   pushAt 2920 2 6272,
   opAt 2921 .MSTORE,
   opAt 2922 .POP,
   opAt 2923 .POP,
   opAt 2924 .POP,
   opAt 2925 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2926 .JUMPDEST,
   opAt 2927 (.Dup ⟨0, by decide⟩),
   opAt 2928 .ISZERO,
   pushAt 2929 2 5375,
   opAt 2930 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2931 (.Dup ⟨1, by decide⟩),
   pushAt 2932 2 2048,
   pushAt 2933 2 8224,
   opAt 2934 .MCOPY,
   pushAt 2935 0 0,
   pushAt 2936 2 9440,
   opAt 2937 .MLOAD,
   opAt 2938 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2939 .JUMPDEST,
   pushAt 2940 2 2048,
   opAt 2941 .MLOAD,
   pushAt 2942 2 6144,
   opAt 2943 .MLOAD,
   opAt 2944 (.Dup ⟨1, by decide⟩),
   opAt 2945 (.Dup ⟨1, by decide⟩),
   opAt 2946 (.Swap ⟨0, by decide⟩),
   opAt 2947 .DIV,
   opAt 2948 (.Swap ⟨1, by decide⟩),
   opAt 2949 .MOD,
   pushAt 2950 2 6208,
   opAt 2951 .MLOAD,
   opAt 2952 .MUL,
   pushAt 2953 2 2080,
   opAt 2954 .MLOAD,
   pushAt 2955 2 6144,
   opAt 2956 .MLOAD,
   opAt 2957 (.Swap ⟨0, by decide⟩),
   opAt 2958 .DIV,
   opAt 2959 .ADD,
   pushAt 2960 2 6176,
   opAt 2961 .MLOAD,
   opAt 2962 (.Dup ⟨0, by decide⟩),
   pushAt 2963 2 6240,
   opAt 2964 .MLOAD,
   opAt 2965 (.Dup ⟨4, by decide⟩),
   opAt 2966 .MULMOD,
   opAt 2967 (.Dup ⟨2, by decide⟩),
   opAt 2968 (.Swap ⟨0, by decide⟩),
   opAt 2969 .ADDMOD,
   opAt 2970 (.Swap ⟨0, by decide⟩),
   opAt 2971 .SUB,
   pushAt 2972 2 6272,
   opAt 2973 .MLOAD,
   opAt 2974 .MUL,
   opAt 2975 (.Dup ⟨0, by decide⟩),
   pushAt 2976 0 0,
   opAt 2977 .LT,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 .SUB,
   opAt 2980 (.Swap ⟨0, by decide⟩),
   pushAt 2981 2 6176,
   opAt 2982 .MLOAD,
   opAt 2983 (.Swap ⟨0, by decide⟩),
   opAt 2984 .LT,
   opAt 2985 .ISZERO,
   pushAt 2986 0 0,
   opAt 2987 .SUB,
   opAt 2988 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2989 .JUMPDEST,
   pushAt 2990 0 0,
   pushAt 2991 2 9440,
   opAt 2992 .MLOAD,
   pushAt 2993 2 9408,
   opAt 2994 .MLOAD,
   pushAt 2995 2 5120,
   opAt 2996 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2997 .JUMPDEST,
   opAt 2998 (.Dup ⟨0, by decide⟩),
   opAt 2999 .MLOAD,
   pushAt 3000 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3001 (.Dup ⟨5, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   opAt 3003 .MUL,
   opAt 3004 (.Swap ⟨1, by decide⟩),
   opAt 3005 (.Dup ⟨6, by decide⟩),
   opAt 3006 .MULMOD,
   opAt 3007 (.Dup ⟨1, by decide⟩),
   opAt 3008 (.Dup ⟨1, by decide⟩),
   opAt 3009 .LT,
   opAt 3010 .SUB,
   opAt 3011 (.Dup ⟨4, by decide⟩),
   opAt 3012 (.Dup ⟨2, by decide⟩),
   opAt 3013 .ADD,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   opAt 3015 (.Swap ⟨5, by decide⟩),
   opAt 3016 .GT,
   opAt 3017 .SUB,
   opAt 3018 .SUB,
   opAt 3019 (.Dup ⟨3, by decide⟩),
   opAt 3020 (.Dup ⟨3, by decide⟩),
   opAt 3021 .MLOAD,
   opAt 3022 .ADD,
   opAt 3023 (.Dup ⟨0, by decide⟩),
   opAt 3024 (.Swap ⟨4, by decide⟩),
   opAt 3025 .GT,
   opAt 3026 .ADD,
   opAt 3027 (.Swap ⟨2, by decide⟩),
   opAt 3028 (.Dup ⟨2, by decide⟩),
   pushAt 3029 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3030 .ADD,
   opAt 3031 (.Swap ⟨2, by decide⟩),
   opAt 3032 .MSTORE,
   pushAt 3033 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3034 .ADD,
   opAt 3035 .JUMPDEST,
   opAt 3036 .JUMPDEST,
   opAt 3037 .JUMPDEST,
   opAt 3038 .JUMPDEST,
   opAt 3039 .JUMPDEST,
   pushAt 3040 2 8224,
   opAt 3041 (.Dup ⟨2, by decide⟩),
   opAt 3042 .GT,
   pushAt 3043 2 4977,
   opAt 3044 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3045 .POP,
   opAt 3046 .POP,
   pushAt 3047 2 8224,
   opAt 3048 .MLOAD,
   opAt 3049 (.Dup ⟨1, by decide⟩),
   opAt 3050 .ADD,
   opAt 3051 (.Dup ⟨1, by decide⟩),
   opAt 3052 (.Dup ⟨1, by decide⟩),
   opAt 3053 .LT,
   opAt 3054 (.Swap ⟨1, by decide⟩),
   opAt 3055 .POP,
   opAt 3056 (.Dup ⟨2, by decide⟩),
   opAt 3057 (.Dup ⟨1, by decide⟩),
   opAt 3058 .LT,
   opAt 3059 (.Swap ⟨0, by decide⟩),
   opAt 3060 (.Dup ⟨3, by decide⟩),
   opAt 3061 (.Swap ⟨0, by decide⟩),
   opAt 3062 .SUB,
   opAt 3063 (.Dup ⟨0, by decide⟩),
   pushAt 3064 2 8224,
   opAt 3065 .MSTORE,
   opAt 3066 .POP,
   opAt 3067 .GT,
   opAt 3068 (.Swap ⟨0, by decide⟩),
   opAt 3069 .POP,
   opAt 3070 .ISZERO,
   pushAt 3071 2 5256,
   opAt 3072 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3073 .JUMPDEST,
   pushAt 3074 0 0,
   pushAt 3075 2 9440,
   opAt 3076 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3077 .JUMPDEST,
   opAt 3078 (.Dup ⟨0, by decide⟩),
   opAt 3079 .MLOAD,
   opAt 3080 (.Dup ⟨1, by decide⟩),
   pushAt 3081 2 8256,
   opAt 3082 (.Swap ⟨0, by decide⟩),
   opAt 3083 .SUB,
   opAt 3084 .MLOAD,
   opAt 3085 (.Dup ⟨1, by decide⟩),
   opAt 3086 .ADD,
   opAt 3087 (.Dup ⟨0, by decide⟩),
   opAt 3088 (.Dup ⟨2, by decide⟩),
   opAt 3089 .GT,
   opAt 3090 (.Swap ⟨1, by decide⟩),
   opAt 3091 .POP,
   opAt 3092 (.Dup ⟨3, by decide⟩),
   opAt 3093 .ADD,
   opAt 3094 (.Dup ⟨0, by decide⟩),
   opAt 3095 (.Dup ⟨4, by decide⟩),
   opAt 3096 .GT,
   opAt 3097 (.Swap ⟨3, by decide⟩),
   opAt 3098 .POP,
   opAt 3099 (.Dup ⟨2, by decide⟩),
   opAt 3100 .MSTORE,
   opAt 3101 (.Swap ⟨0, by decide⟩),
   opAt 3102 (.Swap ⟨1, by decide⟩),
   opAt 3103 .OR,
   opAt 3104 (.Swap ⟨0, by decide⟩),
   pushAt 3105 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3106 .ADD,
   pushAt 3107 2 8255,
   opAt 3108 (.Dup ⟨1, by decide⟩),
   opAt 3109 .GT,
   pushAt 3110 2 5165,
   opAt 3111 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3112 .POP,
   pushAt 3113 2 8224,
   opAt 3114 .MLOAD,
   opAt 3115 (.Dup ⟨1, by decide⟩),
   opAt 3116 .ADD,
   opAt 3117 (.Dup ⟨0, by decide⟩),
   pushAt 3118 2 8224,
   opAt 3119 .MSTORE,
   opAt 3120 .LT,
   opAt 3121 .ISZERO,
   pushAt 3122 2 5159,
   opAt 3123 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3124 .JUMPDEST,
   pushAt 3125 2 8224,
   opAt 3126 .MLOAD,
   opAt 3127 .ISZERO,
   pushAt 3128 2 5355,
   opAt 3129 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3130 0 0,
   pushAt 3131 2 9440,
   opAt 3132 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3133 .JUMPDEST,
   opAt 3134 (.Dup ⟨0, by decide⟩),
   opAt 3135 .MLOAD,
   opAt 3136 (.Dup ⟨1, by decide⟩),
   pushAt 3137 2 8256,
   opAt 3138 (.Swap ⟨0, by decide⟩),
   opAt 3139 .SUB,
   opAt 3140 .MLOAD,
   opAt 3141 (.Dup ⟨1, by decide⟩),
   opAt 3142 (.Dup ⟨1, by decide⟩),
   opAt 3143 .GT,
   opAt 3144 (.Swap ⟨1, by decide⟩),
   opAt 3145 .SUB,
   opAt 3146 (.Dup ⟨3, by decide⟩),
   opAt 3147 (.Dup ⟨1, by decide⟩),
   opAt 3148 .LT,
   opAt 3149 (.Swap ⟨0, by decide⟩),
   opAt 3150 (.Dup ⟨4, by decide⟩),
   opAt 3151 (.Swap ⟨0, by decide⟩),
   opAt 3152 .SUB,
   opAt 3153 (.Dup ⟨3, by decide⟩),
   opAt 3154 .MSTORE,
   opAt 3155 .OR,
   opAt 3156 (.Swap ⟨1, by decide⟩),
   opAt 3157 .POP,
   pushAt 3158 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3159 .ADD,
   pushAt 3160 2 8255,
   opAt 3161 (.Dup ⟨1, by decide⟩),
   opAt 3162 .GT,
   pushAt 3163 2 5271,
   opAt 3164 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3165 .POP,
   pushAt 3166 2 8224,
   opAt 3167 .MLOAD,
   opAt 3168 .SUB,
   pushAt 3169 2 8224,
   opAt 3170 .MSTORE,
   pushAt 3171 2 5256,
   opAt 3172 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3173 .JUMPDEST,
   pushAt 3174 2 5366,
   pushAt 3175 2 2048,
   pushAt 3176 2 2642,
   opAt 3177 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3178 .JUMPDEST,
   pushAt 3179 1 1,
   opAt 3180 (.Swap ⟨0, by decide⟩),
   opAt 3181 .SUB,
   pushAt 3182 2 4874,
   opAt 3183 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3184 .JUMPDEST,
   opAt 3185 .POP,
   pushAt 3186 2 1756,
   opAt 3187 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4643 = true :=
  Artifact.isValidJumpDest_index 2775 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4687 = true :=
  Artifact.isValidJumpDest_index 2802 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4692 = true :=
  Artifact.isValidJumpDest_index 2805 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4699 = true :=
  Artifact.isValidJumpDest_index 2809 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4760 = true :=
  Artifact.isValidJumpDest_index 2832 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4806 = true :=
  Artifact.isValidJumpDest_index 2869 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4837 = true :=
  Artifact.isValidJumpDest_index 2895 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4874 = true :=
  Artifact.isValidJumpDest_index 2926 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4895 = true :=
  Artifact.isValidJumpDest_index 2939 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4963 = true :=
  Artifact.isValidJumpDest_index 2989 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4977 = true :=
  Artifact.isValidJumpDest_index 2997 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5159 = true :=
  Artifact.isValidJumpDest_index 3073 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5165 = true :=
  Artifact.isValidJumpDest_index 3077 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5256 = true :=
  Artifact.isValidJumpDest_index 3124 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5271 = true :=
  Artifact.isValidJumpDest_index 3133 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5355 = true :=
  Artifact.isValidJumpDest_index 3173 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5366 = true :=
  Artifact.isValidJumpDest_index 3178 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5375 = true :=
  Artifact.isValidJumpDest_index 3184 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
