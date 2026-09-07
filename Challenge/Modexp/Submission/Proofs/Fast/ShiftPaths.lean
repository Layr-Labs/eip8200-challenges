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
  [opAt 2734 .JUMPDEST,
   opAt 2735 (.Dup ⟨0, by decide⟩),
   opAt 2736 (.Dup ⟨3, by decide⟩),
   opAt 2737 .EQ,
   pushAt 2738 0 0,
   opAt 2739 .MLOAD,
   pushAt 2740 1 255,
   opAt 2741 .SHR,
   opAt 2742 .AND,
   opAt 2743 .ISZERO,
   pushAt 2744 2 4662,
   opAt 2745 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2746 (.Dup ⟨0, by decide⟩),
   pushAt 2747 1 96,
   pushAt 2748 2 1024,
   opAt 2749 .CALLDATACOPY,
   opAt 2750 (.Dup ⟨0, by decide⟩),
   pushAt 2751 1 96,
   pushAt 2752 2 8256,
   opAt 2753 .CALLDATACOPY,
   pushAt 2754 0 0,
   pushAt 2755 2 8224,
   opAt 2756 .MSTORE,
   pushAt 2757 2 4667,
   pushAt 2758 2 2048,
   pushAt 2759 2 2637,
   opAt 2760 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2761 .JUMPDEST,
   pushAt 2762 2 1533,
   opAt 2763 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2764 .JUMPDEST,
   pushAt 2765 1 1,
   pushAt 2766 2 9408,
   opAt 2767 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2768 .JUMPDEST,
   opAt 2769 (.Dup ⟨0, by decide⟩),
   opAt 2770 .MLOAD,
   opAt 2771 .NOT,
   opAt 2772 (.Dup ⟨2, by decide⟩),
   opAt 2773 .ADD,
   opAt 2774 (.Dup ⟨2, by decide⟩),
   opAt 2775 (.Dup ⟨1, by decide⟩),
   opAt 2776 .LT,
   opAt 2777 (.Swap ⟨2, by decide⟩),
   opAt 2778 .POP,
   opAt 2779 (.Dup ⟨1, by decide⟩),
   pushAt 2780 2 5120,
   opAt 2781 .ADD,
   opAt 2782 .MSTORE,
   opAt 2783 (.Dup ⟨0, by decide⟩),
   opAt 2784 .ISZERO,
   pushAt 2785 2 4735,
   opAt 2786 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2787 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2788 .ADD,
   pushAt 2789 2 4674,
   opAt 2790 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2791 .JUMPDEST,
   opAt 2792 .POP,
   opAt 2793 .POP,
   pushAt 2794 0 0,
   opAt 2795 .MLOAD,
   opAt 2796 (.Dup ⟨0, by decide⟩),
   pushAt 2797 0 0,
   opAt 2798 .SUB,
   opAt 2799 (.Dup ⟨1, by decide⟩),
   opAt 2800 .AND,
   opAt 2801 (.Dup ⟨0, by decide⟩),
   pushAt 2802 2 6144,
   opAt 2803 .MSTORE,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   opAt 2805 (.Dup ⟨2, by decide⟩),
   opAt 2806 .DIV,
   opAt 2807 (.Dup ⟨0, by decide⟩),
   pushAt 2808 2 6176,
   opAt 2809 .MSTORE,
   opAt 2810 (.Dup ⟨1, by decide⟩),
   pushAt 2811 0 0,
   opAt 2812 .SUB,
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 (.Swap ⟨0, by decide⟩),
   opAt 2815 .DIV,
   pushAt 2816 1 1,
   opAt 2817 .ADD,
   pushAt 2818 2 6208,
   opAt 2819 .MSTORE,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   pushAt 2821 0 0,
   opAt 2822 .SUB,
   opAt 2823 (.Dup ⟨1, by decide⟩),
   opAt 2824 (.Swap ⟨0, by decide⟩),
   opAt 2825 .MOD,
   pushAt 2826 2 6240,
   opAt 2827 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2828 .JUMPDEST,
   pushAt 2829 1 1,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 (.Dup ⟨2, by decide⟩),
   opAt 2832 .MUL,
   pushAt 2833 1 2,
   opAt 2834 .SUB,
   opAt 2835 .MUL,
   opAt 2836 (.Dup ⟨0, by decide⟩),
   opAt 2837 (.Dup ⟨2, by decide⟩),
   opAt 2838 .MUL,
   pushAt 2839 1 2,
   opAt 2840 .SUB,
   opAt 2841 .MUL,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   opAt 2843 (.Dup ⟨2, by decide⟩),
   opAt 2844 .MUL,
   pushAt 2845 1 2,
   opAt 2846 .SUB,
   opAt 2847 .MUL,
   opAt 2848 (.Dup ⟨0, by decide⟩),
   opAt 2849 (.Dup ⟨2, by decide⟩),
   opAt 2850 .MUL,
   pushAt 2851 1 2,
   opAt 2852 .SUB,
   opAt 2853 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2854 .JUMPDEST,
   opAt 2855 (.Dup ⟨0, by decide⟩),
   opAt 2856 (.Dup ⟨2, by decide⟩),
   opAt 2857 .MUL,
   pushAt 2858 1 2,
   opAt 2859 .SUB,
   opAt 2860 .MUL,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   opAt 2862 (.Dup ⟨2, by decide⟩),
   opAt 2863 .MUL,
   pushAt 2864 1 2,
   opAt 2865 .SUB,
   opAt 2866 .MUL,
   opAt 2867 (.Dup ⟨0, by decide⟩),
   opAt 2868 (.Dup ⟨2, by decide⟩),
   opAt 2869 .MUL,
   pushAt 2870 1 2,
   opAt 2871 .SUB,
   opAt 2872 .MUL,
   opAt 2873 (.Dup ⟨0, by decide⟩),
   opAt 2874 (.Dup ⟨2, by decide⟩),
   opAt 2875 .MUL,
   pushAt 2876 1 2,
   opAt 2877 .SUB,
   opAt 2878 .MUL,
   pushAt 2879 2 6272,
   opAt 2880 .MSTORE,
   opAt 2881 .POP,
   opAt 2882 .POP,
   opAt 2883 .POP,
   opAt 2884 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2885 .JUMPDEST,
   opAt 2886 (.Dup ⟨0, by decide⟩),
   opAt 2887 .ISZERO,
   pushAt 2888 2 5345,
   opAt 2889 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2890 (.Dup ⟨1, by decide⟩),
   pushAt 2891 2 2048,
   pushAt 2892 2 8224,
   opAt 2893 .MCOPY,
   pushAt 2894 0 0,
   pushAt 2895 2 9440,
   opAt 2896 .MLOAD,
   opAt 2897 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2898 .JUMPDEST,
   pushAt 2899 2 2048,
   opAt 2900 .MLOAD,
   pushAt 2901 2 6144,
   opAt 2902 .MLOAD,
   opAt 2903 (.Dup ⟨1, by decide⟩),
   opAt 2904 (.Dup ⟨1, by decide⟩),
   opAt 2905 (.Swap ⟨0, by decide⟩),
   opAt 2906 .DIV,
   opAt 2907 (.Swap ⟨1, by decide⟩),
   opAt 2908 .MOD,
   pushAt 2909 2 6208,
   opAt 2910 .MLOAD,
   opAt 2911 .MUL,
   pushAt 2912 2 2080,
   opAt 2913 .MLOAD,
   pushAt 2914 2 6144,
   opAt 2915 .MLOAD,
   opAt 2916 (.Swap ⟨0, by decide⟩),
   opAt 2917 .DIV,
   opAt 2918 .ADD,
   pushAt 2919 2 6176,
   opAt 2920 .MLOAD,
   opAt 2921 (.Dup ⟨0, by decide⟩),
   pushAt 2922 2 6240,
   opAt 2923 .MLOAD,
   opAt 2924 (.Dup ⟨4, by decide⟩),
   opAt 2925 .MULMOD,
   opAt 2926 (.Dup ⟨2, by decide⟩),
   opAt 2927 (.Swap ⟨0, by decide⟩),
   opAt 2928 .ADDMOD,
   opAt 2929 (.Swap ⟨0, by decide⟩),
   opAt 2930 .SUB,
   pushAt 2931 2 6272,
   opAt 2932 .MLOAD,
   opAt 2933 .MUL,
   opAt 2934 (.Dup ⟨0, by decide⟩),
   opAt 2935 .ISZERO,
   opAt 2936 .ISZERO,
   opAt 2937 (.Swap ⟨0, by decide⟩),
   opAt 2938 .SUB,
   opAt 2939 (.Swap ⟨0, by decide⟩),
   pushAt 2940 2 6176,
   opAt 2941 .MLOAD,
   opAt 2942 (.Swap ⟨0, by decide⟩),
   opAt 2943 .LT,
   opAt 2944 .ISZERO,
   pushAt 2945 0 0,
   opAt 2946 .SUB,
   opAt 2947 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2948 .JUMPDEST,
   pushAt 2949 0 0,
   pushAt 2950 2 9440,
   opAt 2951 .MLOAD,
   pushAt 2952 2 9408,
   opAt 2953 .MLOAD,
   pushAt 2954 2 5120,
   opAt 2955 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2956 .JUMPDEST,
   opAt 2957 (.Dup ⟨0, by decide⟩),
   opAt 2958 .MLOAD,
   pushAt 2959 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2960 (.Dup ⟨5, by decide⟩),
   opAt 2961 (.Dup ⟨2, by decide⟩),
   opAt 2962 .MUL,
   opAt 2963 (.Swap ⟨1, by decide⟩),
   opAt 2964 (.Dup ⟨6, by decide⟩),
   opAt 2965 .MULMOD,
   opAt 2966 (.Dup ⟨1, by decide⟩),
   opAt 2967 (.Dup ⟨1, by decide⟩),
   opAt 2968 .LT,
   opAt 2969 .SUB,
   opAt 2970 (.Dup ⟨4, by decide⟩),
   opAt 2971 (.Dup ⟨2, by decide⟩),
   opAt 2972 .ADD,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 (.Swap ⟨5, by decide⟩),
   opAt 2975 .GT,
   opAt 2976 .SUB,
   opAt 2977 .SUB,
   opAt 2978 (.Dup ⟨3, by decide⟩),
   opAt 2979 (.Dup ⟨3, by decide⟩),
   opAt 2980 .MLOAD,
   opAt 2981 .ADD,
   opAt 2982 (.Dup ⟨0, by decide⟩),
   opAt 2983 (.Swap ⟨4, by decide⟩),
   opAt 2984 .GT,
   opAt 2985 .ADD,
   opAt 2986 (.Swap ⟨2, by decide⟩),
   opAt 2987 (.Dup ⟨2, by decide⟩),
   pushAt 2988 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2989 .ADD,
   opAt 2990 (.Swap ⟨2, by decide⟩),
   opAt 2991 .MSTORE,
   pushAt 2992 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2993 .ADD,
   pushAt 2994 2 8224,
   opAt 2995 (.Dup ⟨2, by decide⟩),
   opAt 2996 .GT,
   pushAt 2997 2 4952,
   opAt 2998 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2999 .POP,
   opAt 3000 .POP,
   pushAt 3001 2 8224,
   opAt 3002 .MLOAD,
   opAt 3003 (.Dup ⟨1, by decide⟩),
   opAt 3004 .ADD,
   opAt 3005 (.Dup ⟨1, by decide⟩),
   opAt 3006 (.Dup ⟨1, by decide⟩),
   opAt 3007 .LT,
   opAt 3008 (.Swap ⟨1, by decide⟩),
   opAt 3009 .POP,
   opAt 3010 (.Dup ⟨2, by decide⟩),
   opAt 3011 (.Dup ⟨1, by decide⟩),
   opAt 3012 .LT,
   opAt 3013 (.Swap ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨3, by decide⟩),
   opAt 3015 (.Swap ⟨0, by decide⟩),
   opAt 3016 .SUB,
   opAt 3017 (.Dup ⟨0, by decide⟩),
   pushAt 3018 2 8224,
   opAt 3019 .MSTORE,
   opAt 3020 .POP,
   opAt 3021 .GT,
   opAt 3022 (.Swap ⟨0, by decide⟩),
   opAt 3023 .POP,
   opAt 3024 .ISZERO,
   pushAt 3025 2 5226,
   opAt 3026 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3027 .JUMPDEST,
   pushAt 3028 0 0,
   pushAt 3029 2 9440,
   opAt 3030 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3031 .JUMPDEST,
   opAt 3032 (.Dup ⟨0, by decide⟩),
   opAt 3033 .MLOAD,
   opAt 3034 (.Dup ⟨1, by decide⟩),
   pushAt 3035 2 8256,
   opAt 3036 (.Swap ⟨0, by decide⟩),
   opAt 3037 .SUB,
   opAt 3038 .MLOAD,
   opAt 3039 (.Dup ⟨1, by decide⟩),
   opAt 3040 .ADD,
   opAt 3041 (.Dup ⟨0, by decide⟩),
   opAt 3042 (.Dup ⟨2, by decide⟩),
   opAt 3043 .GT,
   opAt 3044 (.Swap ⟨1, by decide⟩),
   opAt 3045 .POP,
   opAt 3046 (.Dup ⟨3, by decide⟩),
   opAt 3047 .ADD,
   opAt 3048 (.Dup ⟨0, by decide⟩),
   opAt 3049 (.Dup ⟨4, by decide⟩),
   opAt 3050 .GT,
   opAt 3051 (.Swap ⟨3, by decide⟩),
   opAt 3052 .POP,
   opAt 3053 (.Dup ⟨2, by decide⟩),
   opAt 3054 .MSTORE,
   opAt 3055 (.Swap ⟨0, by decide⟩),
   opAt 3056 (.Swap ⟨1, by decide⟩),
   opAt 3057 .OR,
   opAt 3058 (.Swap ⟨0, by decide⟩),
   pushAt 3059 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3060 .ADD,
   pushAt 3061 2 8255,
   opAt 3062 (.Dup ⟨1, by decide⟩),
   opAt 3063 .GT,
   pushAt 3064 2 5135,
   opAt 3065 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3066 .POP,
   pushAt 3067 2 8224,
   opAt 3068 .MLOAD,
   opAt 3069 (.Dup ⟨1, by decide⟩),
   opAt 3070 .ADD,
   opAt 3071 (.Dup ⟨0, by decide⟩),
   pushAt 3072 2 8224,
   opAt 3073 .MSTORE,
   opAt 3074 .LT,
   opAt 3075 .ISZERO,
   pushAt 3076 2 5129,
   opAt 3077 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3078 .JUMPDEST,
   pushAt 3079 2 8224,
   opAt 3080 .MLOAD,
   opAt 3081 .ISZERO,
   pushAt 3082 2 5325,
   opAt 3083 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3084 0 0,
   pushAt 3085 2 9440,
   opAt 3086 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3087 .JUMPDEST,
   opAt 3088 (.Dup ⟨0, by decide⟩),
   opAt 3089 .MLOAD,
   opAt 3090 (.Dup ⟨1, by decide⟩),
   pushAt 3091 2 8256,
   opAt 3092 (.Swap ⟨0, by decide⟩),
   opAt 3093 .SUB,
   opAt 3094 .MLOAD,
   opAt 3095 (.Dup ⟨1, by decide⟩),
   opAt 3096 (.Dup ⟨1, by decide⟩),
   opAt 3097 .GT,
   opAt 3098 (.Swap ⟨1, by decide⟩),
   opAt 3099 .SUB,
   opAt 3100 (.Dup ⟨3, by decide⟩),
   opAt 3101 (.Dup ⟨1, by decide⟩),
   opAt 3102 .LT,
   opAt 3103 (.Swap ⟨0, by decide⟩),
   opAt 3104 (.Dup ⟨4, by decide⟩),
   opAt 3105 (.Swap ⟨0, by decide⟩),
   opAt 3106 .SUB,
   opAt 3107 (.Dup ⟨3, by decide⟩),
   opAt 3108 .MSTORE,
   opAt 3109 .OR,
   opAt 3110 (.Swap ⟨1, by decide⟩),
   opAt 3111 .POP,
   pushAt 3112 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3113 .ADD,
   pushAt 3114 2 8255,
   opAt 3115 (.Dup ⟨1, by decide⟩),
   opAt 3116 .GT,
   pushAt 3117 2 5241,
   opAt 3118 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3119 .POP,
   pushAt 3120 2 8224,
   opAt 3121 .MLOAD,
   opAt 3122 .SUB,
   pushAt 3123 2 8224,
   opAt 3124 .MSTORE,
   pushAt 3125 2 5226,
   opAt 3126 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3127 .JUMPDEST,
   pushAt 3128 2 5336,
   pushAt 3129 2 2048,
   pushAt 3130 2 2637,
   opAt 3131 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3132 .JUMPDEST,
   pushAt 3133 1 1,
   opAt 3134 (.Swap ⟨0, by decide⟩),
   opAt 3135 .SUB,
   pushAt 3136 2 4849,
   opAt 3137 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3138 .JUMPDEST,
   opAt 3139 .POP,
   pushAt 3140 2 1756,
   opAt 3141 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4618 = true :=
  Artifact.isValidJumpDest_index 2734 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4662 = true :=
  Artifact.isValidJumpDest_index 2761 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4667 = true :=
  Artifact.isValidJumpDest_index 2764 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4674 = true :=
  Artifact.isValidJumpDest_index 2768 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 2791 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4781 = true :=
  Artifact.isValidJumpDest_index 2828 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4812 = true :=
  Artifact.isValidJumpDest_index 2854 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4849 = true :=
  Artifact.isValidJumpDest_index 2885 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4870 = true :=
  Artifact.isValidJumpDest_index 2898 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4938 = true :=
  Artifact.isValidJumpDest_index 2948 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4952 = true :=
  Artifact.isValidJumpDest_index 2956 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5129 = true :=
  Artifact.isValidJumpDest_index 3027 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5135 = true :=
  Artifact.isValidJumpDest_index 3031 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5226 = true :=
  Artifact.isValidJumpDest_index 3078 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5241 = true :=
  Artifact.isValidJumpDest_index 3087 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5325 = true :=
  Artifact.isValidJumpDest_index 3127 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5336 = true :=
  Artifact.isValidJumpDest_index 3132 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5345 = true :=
  Artifact.isValidJumpDest_index 3138 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
