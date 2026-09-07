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
   pushAt 2774 2 4605,
   opAt 2775 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
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
   pushAt 2787 2 4610,
   pushAt 2788 2 2048,
   pushAt 2789 2 2642,
   opAt 2790 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2791 .JUMPDEST,
   pushAt 2792 2 1533,
   opAt 2793 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2794 .JUMPDEST,
   pushAt 2795 1 1,
   pushAt 2796 2 9408,
   opAt 2797 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
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
   pushAt 2815 2 4678,
   opAt 2816 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2817 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2818 .ADD,
   pushAt 2819 2 4617,
   opAt 2820 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2821 .JUMPDEST,
   opAt 2822 .POP,
   opAt 2823 .POP,
   pushAt 2824 0 0,
   opAt 2825 .MLOAD,
   opAt 2826 (.Dup ⟨0, by decide⟩),
   pushAt 2827 0 0,
   opAt 2828 .SUB,
   opAt 2829 (.Dup ⟨1, by decide⟩),
   opAt 2830 .AND,
   opAt 2831 (.Dup ⟨0, by decide⟩),
   pushAt 2832 2 6144,
   opAt 2833 .MSTORE,
   opAt 2834 (.Dup ⟨0, by decide⟩),
   opAt 2835 (.Dup ⟨2, by decide⟩),
   opAt 2836 .DIV,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   pushAt 2838 2 6176,
   opAt 2839 .MSTORE,
   opAt 2840 (.Dup ⟨1, by decide⟩),
   pushAt 2841 0 0,
   opAt 2842 .SUB,
   opAt 2843 (.Dup ⟨2, by decide⟩),
   opAt 2844 (.Swap ⟨0, by decide⟩),
   opAt 2845 .DIV,
   pushAt 2846 1 1,
   opAt 2847 .ADD,
   pushAt 2848 2 6208,
   opAt 2849 .MSTORE,
   opAt 2850 (.Dup ⟨0, by decide⟩),
   pushAt 2851 0 0,
   opAt 2852 .SUB,
   opAt 2853 (.Dup ⟨1, by decide⟩),
   opAt 2854 (.Swap ⟨0, by decide⟩),
   opAt 2855 .MOD,
   pushAt 2856 2 6240,
   opAt 2857 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2858 .JUMPDEST,
   pushAt 2859 1 1,
   opAt 2860 (.Dup ⟨0, by decide⟩),
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
   opAt 2883 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2884 .JUMPDEST,
   opAt 2885 (.Dup ⟨0, by decide⟩),
   opAt 2886 (.Dup ⟨2, by decide⟩),
   opAt 2887 .MUL,
   pushAt 2888 1 2,
   opAt 2889 .SUB,
   opAt 2890 .MUL,
   opAt 2891 (.Dup ⟨0, by decide⟩),
   opAt 2892 (.Dup ⟨2, by decide⟩),
   opAt 2893 .MUL,
   pushAt 2894 1 2,
   opAt 2895 .SUB,
   opAt 2896 .MUL,
   opAt 2897 (.Dup ⟨0, by decide⟩),
   opAt 2898 (.Dup ⟨2, by decide⟩),
   opAt 2899 .MUL,
   pushAt 2900 1 2,
   opAt 2901 .SUB,
   opAt 2902 .MUL,
   opAt 2903 (.Dup ⟨0, by decide⟩),
   opAt 2904 (.Dup ⟨2, by decide⟩),
   opAt 2905 .MUL,
   pushAt 2906 1 2,
   opAt 2907 .SUB,
   opAt 2908 .MUL,
   pushAt 2909 2 6272,
   opAt 2910 .MSTORE,
   opAt 2911 .POP,
   opAt 2912 .POP,
   opAt 2913 .POP,
   opAt 2914 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2915 .JUMPDEST,
   opAt 2916 (.Dup ⟨0, by decide⟩),
   opAt 2917 .ISZERO,
   pushAt 2918 2 5284,
   opAt 2919 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2920 (.Dup ⟨1, by decide⟩),
   pushAt 2921 2 2048,
   pushAt 2922 2 8224,
   opAt 2923 .MCOPY,
   pushAt 2924 0 0,
   pushAt 2925 2 9440,
   opAt 2926 .MLOAD,
   opAt 2927 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2928 .JUMPDEST,
   pushAt 2929 2 2048,
   opAt 2930 .MLOAD,
   pushAt 2931 2 6144,
   opAt 2932 .MLOAD,
   opAt 2933 (.Dup ⟨1, by decide⟩),
   opAt 2934 (.Dup ⟨1, by decide⟩),
   opAt 2935 (.Swap ⟨0, by decide⟩),
   opAt 2936 .DIV,
   opAt 2937 (.Swap ⟨1, by decide⟩),
   opAt 2938 .MOD,
   pushAt 2939 2 6208,
   opAt 2940 .MLOAD,
   opAt 2941 .MUL,
   pushAt 2942 2 2080,
   opAt 2943 .MLOAD,
   pushAt 2944 2 6144,
   opAt 2945 .MLOAD,
   opAt 2946 (.Swap ⟨0, by decide⟩),
   opAt 2947 .DIV,
   opAt 2948 .ADD,
   pushAt 2949 2 6176,
   opAt 2950 .MLOAD,
   opAt 2951 (.Dup ⟨0, by decide⟩),
   pushAt 2952 2 6240,
   opAt 2953 .MLOAD,
   opAt 2954 (.Dup ⟨4, by decide⟩),
   opAt 2955 .MULMOD,
   opAt 2956 (.Dup ⟨2, by decide⟩),
   opAt 2957 (.Swap ⟨0, by decide⟩),
   opAt 2958 .ADDMOD,
   opAt 2959 (.Swap ⟨0, by decide⟩),
   opAt 2960 .SUB,
   pushAt 2961 2 6272,
   opAt 2962 .MLOAD,
   opAt 2963 .MUL,
   opAt 2964 (.Dup ⟨0, by decide⟩),
   opAt 2965 .ISZERO,
   opAt 2966 .ISZERO,
   opAt 2967 (.Swap ⟨0, by decide⟩),
   opAt 2968 .SUB,
   opAt 2969 (.Swap ⟨0, by decide⟩),
   opAt 2970 .POP]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2971 .JUMPDEST,
   pushAt 2972 0 0,
   pushAt 2973 2 9440,
   opAt 2974 .MLOAD,
   pushAt 2975 2 9408,
   opAt 2976 .MLOAD,
   pushAt 2977 2 5120,
   opAt 2978 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2979 .JUMPDEST,
   opAt 2980 (.Dup ⟨3, by decide⟩),
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 .MLOAD,
   opAt 2983 (.Dup ⟨1, by decide⟩),
   opAt 2984 (.Dup ⟨1, by decide⟩),
   opAt 2985 .MUL,
   opAt 2986 (.Swap ⟨1, by decide⟩),
   pushAt 2987 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2988 (.Swap ⟨1, by decide⟩),
   opAt 2989 .MULMOD,
   opAt 2990 (.Dup ⟨1, by decide⟩),
   opAt 2991 (.Dup ⟨1, by decide⟩),
   opAt 2992 .LT,
   opAt 2993 (.Dup ⟨2, by decide⟩),
   opAt 2994 .ADD,
   opAt 2995 (.Swap ⟨0, by decide⟩),
   opAt 2996 .SUB,
   opAt 2997 (.Dup ⟨3, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 (.Swap ⟨1, by decide⟩),
   opAt 3000 (.Dup ⟨2, by decide⟩),
   opAt 3001 .ADD,
   opAt 3002 (.Swap ⟨1, by decide⟩),
   opAt 3003 (.Dup ⟨2, by decide⟩),
   opAt 3004 .LT,
   opAt 3005 .ADD,
   opAt 3006 (.Swap ⟨0, by decide⟩),
   opAt 3007 (.Dup ⟨4, by decide⟩),
   opAt 3008 .ADD,
   opAt 3009 (.Swap ⟨3, by decide⟩),
   opAt 3010 (.Dup ⟨4, by decide⟩),
   opAt 3011 .LT,
   opAt 3012 .ADD,
   opAt 3013 (.Swap ⟨2, by decide⟩),
   opAt 3014 (.Dup ⟨2, by decide⟩),
   opAt 3015 .MSTORE,
   pushAt 3016 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3017 .ADD,
   opAt 3018 (.Swap ⟨0, by decide⟩),
   pushAt 3019 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3020 .ADD,
   opAt 3021 (.Swap ⟨0, by decide⟩),
   pushAt 3022 2 8224,
   opAt 3023 (.Dup ⟨2, by decide⟩),
   opAt 3024 .GT,
   pushAt 3025 2 4886,
   opAt 3026 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3027 .POP,
   opAt 3028 .POP,
   pushAt 3029 2 8224,
   opAt 3030 .MLOAD,
   opAt 3031 (.Dup ⟨1, by decide⟩),
   opAt 3032 .ADD,
   opAt 3033 (.Dup ⟨1, by decide⟩),
   opAt 3034 (.Dup ⟨1, by decide⟩),
   opAt 3035 .LT,
   opAt 3036 (.Swap ⟨1, by decide⟩),
   opAt 3037 .POP,
   opAt 3038 (.Dup ⟨2, by decide⟩),
   opAt 3039 (.Dup ⟨1, by decide⟩),
   opAt 3040 .LT,
   opAt 3041 (.Swap ⟨0, by decide⟩),
   opAt 3042 (.Dup ⟨3, by decide⟩),
   opAt 3043 (.Swap ⟨0, by decide⟩),
   opAt 3044 .SUB,
   opAt 3045 (.Dup ⟨0, by decide⟩),
   pushAt 3046 2 8224,
   opAt 3047 .MSTORE,
   opAt 3048 .POP,
   opAt 3049 .GT,
   opAt 3050 (.Swap ⟨0, by decide⟩),
   opAt 3051 .POP,
   opAt 3052 .ISZERO,
   pushAt 3053 2 5165,
   opAt 3054 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3055 .JUMPDEST,
   pushAt 3056 0 0,
   pushAt 3057 2 9440,
   opAt 3058 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3059 .JUMPDEST,
   opAt 3060 (.Dup ⟨0, by decide⟩),
   opAt 3061 .MLOAD,
   opAt 3062 (.Dup ⟨1, by decide⟩),
   pushAt 3063 2 8256,
   opAt 3064 (.Swap ⟨0, by decide⟩),
   opAt 3065 .SUB,
   opAt 3066 .MLOAD,
   opAt 3067 (.Dup ⟨1, by decide⟩),
   opAt 3068 .ADD,
   opAt 3069 (.Dup ⟨0, by decide⟩),
   opAt 3070 (.Dup ⟨2, by decide⟩),
   opAt 3071 .GT,
   opAt 3072 (.Swap ⟨1, by decide⟩),
   opAt 3073 .POP,
   opAt 3074 (.Dup ⟨3, by decide⟩),
   opAt 3075 .ADD,
   opAt 3076 (.Dup ⟨0, by decide⟩),
   opAt 3077 (.Dup ⟨4, by decide⟩),
   opAt 3078 .GT,
   opAt 3079 (.Swap ⟨3, by decide⟩),
   opAt 3080 .POP,
   opAt 3081 (.Dup ⟨2, by decide⟩),
   opAt 3082 .MSTORE,
   opAt 3083 (.Swap ⟨0, by decide⟩),
   opAt 3084 (.Swap ⟨1, by decide⟩),
   opAt 3085 .OR,
   opAt 3086 (.Swap ⟨0, by decide⟩),
   pushAt 3087 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3088 .ADD,
   pushAt 3089 2 8255,
   opAt 3090 (.Dup ⟨1, by decide⟩),
   opAt 3091 .GT,
   pushAt 3092 2 5074,
   opAt 3093 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3094 .POP,
   pushAt 3095 2 8224,
   opAt 3096 .MLOAD,
   opAt 3097 (.Dup ⟨1, by decide⟩),
   opAt 3098 .ADD,
   opAt 3099 (.Dup ⟨0, by decide⟩),
   pushAt 3100 2 8224,
   opAt 3101 .MSTORE,
   opAt 3102 .LT,
   opAt 3103 .ISZERO,
   pushAt 3104 2 5068,
   opAt 3105 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3106 .JUMPDEST,
   pushAt 3107 2 8224,
   opAt 3108 .MLOAD,
   opAt 3109 .ISZERO,
   pushAt 3110 2 5264,
   opAt 3111 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3112 0 0,
   pushAt 3113 2 9440,
   opAt 3114 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3115 .JUMPDEST,
   opAt 3116 (.Dup ⟨0, by decide⟩),
   opAt 3117 .MLOAD,
   opAt 3118 (.Dup ⟨1, by decide⟩),
   pushAt 3119 2 8256,
   opAt 3120 (.Swap ⟨0, by decide⟩),
   opAt 3121 .SUB,
   opAt 3122 .MLOAD,
   opAt 3123 (.Dup ⟨1, by decide⟩),
   opAt 3124 (.Dup ⟨1, by decide⟩),
   opAt 3125 .GT,
   opAt 3126 (.Swap ⟨1, by decide⟩),
   opAt 3127 .SUB,
   opAt 3128 (.Dup ⟨3, by decide⟩),
   opAt 3129 (.Dup ⟨1, by decide⟩),
   opAt 3130 .LT,
   opAt 3131 (.Swap ⟨0, by decide⟩),
   opAt 3132 (.Dup ⟨4, by decide⟩),
   opAt 3133 (.Swap ⟨0, by decide⟩),
   opAt 3134 .SUB,
   opAt 3135 (.Dup ⟨3, by decide⟩),
   opAt 3136 .MSTORE,
   opAt 3137 .OR,
   opAt 3138 (.Swap ⟨1, by decide⟩),
   opAt 3139 .POP,
   pushAt 3140 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3141 .ADD,
   pushAt 3142 2 8255,
   opAt 3143 (.Dup ⟨1, by decide⟩),
   opAt 3144 .GT,
   pushAt 3145 2 5180,
   opAt 3146 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3147 .POP,
   pushAt 3148 2 8224,
   opAt 3149 .MLOAD,
   opAt 3150 .SUB,
   pushAt 3151 2 8224,
   opAt 3152 .MSTORE,
   pushAt 3153 2 5165,
   opAt 3154 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3155 .JUMPDEST,
   pushAt 3156 2 5275,
   pushAt 3157 2 2048,
   pushAt 3158 2 2642,
   opAt 3159 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3160 .JUMPDEST,
   pushAt 3161 1 1,
   opAt 3162 (.Swap ⟨0, by decide⟩),
   opAt 3163 .SUB,
   pushAt 3164 2 4792,
   opAt 3165 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3166 .JUMPDEST,
   opAt 3167 .POP,
   pushAt 3168 2 1756,
   opAt 3169 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4561 = true :=
  Artifact.isValidJumpDest_index 2764 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4605 = true :=
  Artifact.isValidJumpDest_index 2791 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4610 = true :=
  Artifact.isValidJumpDest_index 2794 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4617 = true :=
  Artifact.isValidJumpDest_index 2798 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4678 = true :=
  Artifact.isValidJumpDest_index 2821 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4724 = true :=
  Artifact.isValidJumpDest_index 2858 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4755 = true :=
  Artifact.isValidJumpDest_index 2884 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4792 = true :=
  Artifact.isValidJumpDest_index 2915 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4813 = true :=
  Artifact.isValidJumpDest_index 2928 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4872 = true :=
  Artifact.isValidJumpDest_index 2971 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4886 = true :=
  Artifact.isValidJumpDest_index 2979 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5068 = true :=
  Artifact.isValidJumpDest_index 3055 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5074 = true :=
  Artifact.isValidJumpDest_index 3059 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5165 = true :=
  Artifact.isValidJumpDest_index 3106 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5180 = true :=
  Artifact.isValidJumpDest_index 3115 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5264 = true :=
  Artifact.isValidJumpDest_index 3155 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5275 = true :=
  Artifact.isValidJumpDest_index 3160 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5284 = true :=
  Artifact.isValidJumpDest_index 3166 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
