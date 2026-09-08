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
  [opAt 2718 .JUMPDEST,
   opAt 2719 (.Dup ⟨0, by decide⟩),
   opAt 2720 (.Dup ⟨3, by decide⟩),
   opAt 2721 .EQ,
   pushAt 2722 0 0,
   opAt 2723 .MLOAD,
   pushAt 2724 1 255,
   opAt 2725 .SHR,
   opAt 2726 .AND,
   opAt 2727 .ISZERO,
   pushAt 2728 2 4662,
   opAt 2729 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2730 (.Dup ⟨0, by decide⟩),
   pushAt 2731 1 96,
   pushAt 2732 2 1024,
   opAt 2733 .CALLDATACOPY,
   opAt 2734 (.Dup ⟨0, by decide⟩),
   pushAt 2735 1 96,
   pushAt 2736 2 8256,
   opAt 2737 .CALLDATACOPY,
   pushAt 2738 0 0,
   pushAt 2739 2 8224,
   opAt 2740 .MSTORE,
   pushAt 2741 2 4667,
   pushAt 2742 2 2048,
   pushAt 2743 2 2637,
   opAt 2744 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2745 .JUMPDEST,
   pushAt 2746 2 1533,
   opAt 2747 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2748 .JUMPDEST,
   pushAt 2749 1 1,
   pushAt 2750 2 9408,
   opAt 2751 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2752 .JUMPDEST,
   opAt 2753 (.Dup ⟨0, by decide⟩),
   opAt 2754 .MLOAD,
   opAt 2755 .NOT,
   opAt 2756 (.Dup ⟨2, by decide⟩),
   opAt 2757 .ADD,
   opAt 2758 (.Dup ⟨2, by decide⟩),
   opAt 2759 (.Dup ⟨1, by decide⟩),
   opAt 2760 .LT,
   opAt 2761 (.Swap ⟨2, by decide⟩),
   opAt 2762 .POP,
   opAt 2763 (.Dup ⟨1, by decide⟩),
   pushAt 2764 2 5120,
   opAt 2765 .ADD,
   opAt 2766 .MSTORE,
   opAt 2767 (.Dup ⟨0, by decide⟩),
   opAt 2768 .ISZERO,
   pushAt 2769 2 4735,
   opAt 2770 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2771 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2772 .ADD,
   pushAt 2773 2 4674,
   opAt 2774 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2775 .JUMPDEST,
   opAt 2776 .POP,
   opAt 2777 .POP,
   pushAt 2778 0 0,
   opAt 2779 .MLOAD,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   pushAt 2781 0 0,
   opAt 2782 .SUB,
   opAt 2783 (.Dup ⟨1, by decide⟩),
   opAt 2784 .AND,
   opAt 2785 (.Dup ⟨0, by decide⟩),
   pushAt 2786 2 6144,
   opAt 2787 .MSTORE,
   opAt 2788 (.Dup ⟨0, by decide⟩),
   opAt 2789 (.Dup ⟨2, by decide⟩),
   opAt 2790 .DIV,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   pushAt 2792 2 6176,
   opAt 2793 .MSTORE,
   opAt 2794 (.Dup ⟨1, by decide⟩),
   pushAt 2795 0 0,
   opAt 2796 .SUB,
   opAt 2797 (.Dup ⟨2, by decide⟩),
   opAt 2798 (.Swap ⟨0, by decide⟩),
   opAt 2799 .DIV,
   pushAt 2800 1 1,
   opAt 2801 .ADD,
   pushAt 2802 2 6208,
   opAt 2803 .MSTORE,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   pushAt 2805 0 0,
   opAt 2806 .SUB,
   opAt 2807 (.Dup ⟨1, by decide⟩),
   opAt 2808 (.Swap ⟨0, by decide⟩),
   opAt 2809 .MOD,
   pushAt 2810 2 6240,
   opAt 2811 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2812 .JUMPDEST,
   pushAt 2813 1 1,
   opAt 2814 (.Dup ⟨0, by decide⟩),
   opAt 2815 (.Dup ⟨2, by decide⟩),
   opAt 2816 .MUL,
   pushAt 2817 1 2,
   opAt 2818 .SUB,
   opAt 2819 .MUL,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   opAt 2821 (.Dup ⟨2, by decide⟩),
   opAt 2822 .MUL,
   pushAt 2823 1 2,
   opAt 2824 .SUB,
   opAt 2825 .MUL,
   opAt 2826 (.Dup ⟨0, by decide⟩),
   opAt 2827 (.Dup ⟨2, by decide⟩),
   opAt 2828 .MUL,
   pushAt 2829 1 2,
   opAt 2830 .SUB,
   opAt 2831 .MUL,
   opAt 2832 (.Dup ⟨0, by decide⟩),
   opAt 2833 (.Dup ⟨2, by decide⟩),
   opAt 2834 .MUL,
   pushAt 2835 1 2,
   opAt 2836 .SUB,
   opAt 2837 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2838 .JUMPDEST,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 (.Dup ⟨2, by decide⟩),
   opAt 2841 .MUL,
   pushAt 2842 1 2,
   opAt 2843 .SUB,
   opAt 2844 .MUL,
   opAt 2845 (.Dup ⟨0, by decide⟩),
   opAt 2846 (.Dup ⟨2, by decide⟩),
   opAt 2847 .MUL,
   pushAt 2848 1 2,
   opAt 2849 .SUB,
   opAt 2850 .MUL,
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
   pushAt 2863 2 6272,
   opAt 2864 .MSTORE,
   opAt 2865 .POP,
   opAt 2866 .POP,
   opAt 2867 .POP,
   opAt 2868 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2869 .JUMPDEST,
   opAt 2870 (.Dup ⟨0, by decide⟩),
   opAt 2871 .ISZERO,
   pushAt 2872 2 5345,
   opAt 2873 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2874 (.Dup ⟨1, by decide⟩),
   pushAt 2875 2 2048,
   pushAt 2876 2 8224,
   opAt 2877 .MCOPY,
   pushAt 2878 0 0,
   pushAt 2879 2 9440,
   opAt 2880 .MLOAD,
   opAt 2881 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2882 .JUMPDEST,
   pushAt 2883 2 2048,
   opAt 2884 .MLOAD,
   pushAt 2885 2 6144,
   opAt 2886 .MLOAD,
   opAt 2887 (.Dup ⟨1, by decide⟩),
   opAt 2888 (.Dup ⟨1, by decide⟩),
   opAt 2889 (.Swap ⟨0, by decide⟩),
   opAt 2890 .DIV,
   opAt 2891 (.Swap ⟨1, by decide⟩),
   opAt 2892 .MOD,
   pushAt 2893 2 6208,
   opAt 2894 .MLOAD,
   opAt 2895 .MUL,
   pushAt 2896 2 2080,
   opAt 2897 .MLOAD,
   pushAt 2898 2 6144,
   opAt 2899 .MLOAD,
   opAt 2900 (.Swap ⟨0, by decide⟩),
   opAt 2901 .DIV,
   opAt 2902 .ADD,
   pushAt 2903 2 6176,
   opAt 2904 .MLOAD,
   opAt 2905 (.Dup ⟨0, by decide⟩),
   pushAt 2906 2 6240,
   opAt 2907 .MLOAD,
   opAt 2908 (.Dup ⟨4, by decide⟩),
   opAt 2909 .MULMOD,
   opAt 2910 (.Dup ⟨2, by decide⟩),
   opAt 2911 .JUMPDEST,
   opAt 2912 .ADDMOD,
   opAt 2913 (.Swap ⟨0, by decide⟩),
   opAt 2914 .SUB,
   pushAt 2915 2 6272,
   opAt 2916 .MLOAD,
   opAt 2917 .MUL,
   opAt 2918 (.Dup ⟨0, by decide⟩),
   pushAt 2919 0 0,
   opAt 2920 .LT,
   opAt 2921 (.Swap ⟨0, by decide⟩),
   opAt 2922 .SUB,
   opAt 2923 (.Swap ⟨0, by decide⟩),
   pushAt 2924 2 6176,
   opAt 2925 .MLOAD,
   opAt 2926 .JUMPDEST,
   opAt 2927 .GT,
   opAt 2928 .ISZERO,
   pushAt 2929 0 0,
   opAt 2930 .SUB,
   opAt 2931 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2932 .JUMPDEST,
   pushAt 2933 0 0,
   pushAt 2934 2 9440,
   opAt 2935 .MLOAD,
   pushAt 2936 2 9408,
   opAt 2937 .MLOAD,
   pushAt 2938 2 5120,
   opAt 2939 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2940 .JUMPDEST,
   opAt 2941 (.Dup ⟨0, by decide⟩),
   opAt 2942 .MLOAD,
   pushAt 2943 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2944 (.Dup ⟨5, by decide⟩),
   opAt 2945 (.Dup ⟨2, by decide⟩),
   opAt 2946 .MUL,
   opAt 2947 (.Swap ⟨1, by decide⟩),
   opAt 2948 (.Dup ⟨6, by decide⟩),
   opAt 2949 .MULMOD,
   opAt 2950 (.Dup ⟨1, by decide⟩),
   opAt 2951 (.Dup ⟨1, by decide⟩),
   opAt 2952 .LT,
   opAt 2953 .SUB,
   opAt 2954 (.Dup ⟨4, by decide⟩),
   opAt 2955 (.Dup ⟨2, by decide⟩),
   opAt 2956 .ADD,
   opAt 2957 (.Dup ⟨0, by decide⟩),
   opAt 2958 (.Swap ⟨5, by decide⟩),
   opAt 2959 .GT,
   opAt 2960 .SUB,
   opAt 2961 .SUB,
   opAt 2962 (.Dup ⟨3, by decide⟩),
   opAt 2963 (.Dup ⟨3, by decide⟩),
   opAt 2964 .MLOAD,
   opAt 2965 .ADD,
   opAt 2966 (.Dup ⟨0, by decide⟩),
   opAt 2967 (.Swap ⟨4, by decide⟩),
   opAt 2968 .GT,
   opAt 2969 .ADD,
   opAt 2970 (.Swap ⟨2, by decide⟩),
   opAt 2971 (.Dup ⟨2, by decide⟩),
   pushAt 2972 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2973 .ADD,
   opAt 2974 (.Swap ⟨2, by decide⟩),
   opAt 2975 .MSTORE,
   pushAt 2976 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2977 .ADD,
   pushAt 2978 2 8224,
   opAt 2979 (.Dup ⟨2, by decide⟩),
   opAt 2980 .GT,
   pushAt 2981 2 4952,
   opAt 2982 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2983 .POP,
   opAt 2984 .POP,
   pushAt 2985 2 8224,
   opAt 2986 .MLOAD,
   opAt 2987 (.Dup ⟨1, by decide⟩),
   opAt 2988 .ADD,
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 (.Dup ⟨1, by decide⟩),
   opAt 2991 .LT,
   opAt 2992 (.Swap ⟨1, by decide⟩),
   opAt 2993 .POP,
   opAt 2994 (.Dup ⟨2, by decide⟩),
   opAt 2995 (.Dup ⟨1, by decide⟩),
   opAt 2996 .LT,
   opAt 2997 (.Swap ⟨0, by decide⟩),
   opAt 2998 (.Dup ⟨3, by decide⟩),
   opAt 2999 (.Swap ⟨0, by decide⟩),
   opAt 3000 .SUB,
   opAt 3001 (.Dup ⟨0, by decide⟩),
   pushAt 3002 2 8224,
   opAt 3003 .MSTORE,
   opAt 3004 .POP,
   opAt 3005 .GT,
   opAt 3006 (.Swap ⟨0, by decide⟩),
   opAt 3007 .POP,
   opAt 3008 .ISZERO,
   pushAt 3009 2 5226,
   opAt 3010 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3011 .JUMPDEST,
   pushAt 3012 0 0,
   pushAt 3013 2 9440,
   opAt 3014 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3015 .JUMPDEST,
   opAt 3016 (.Dup ⟨0, by decide⟩),
   opAt 3017 .MLOAD,
   opAt 3018 (.Dup ⟨1, by decide⟩),
   pushAt 3019 2 8256,
   opAt 3020 (.Swap ⟨0, by decide⟩),
   opAt 3021 .SUB,
   opAt 3022 .MLOAD,
   opAt 3023 (.Dup ⟨1, by decide⟩),
   opAt 3024 .ADD,
   opAt 3025 (.Dup ⟨0, by decide⟩),
   opAt 3026 (.Dup ⟨2, by decide⟩),
   opAt 3027 .GT,
   opAt 3028 (.Swap ⟨1, by decide⟩),
   opAt 3029 .POP,
   opAt 3030 (.Dup ⟨3, by decide⟩),
   opAt 3031 .ADD,
   opAt 3032 (.Dup ⟨0, by decide⟩),
   opAt 3033 (.Dup ⟨4, by decide⟩),
   opAt 3034 .GT,
   opAt 3035 (.Swap ⟨3, by decide⟩),
   opAt 3036 .POP,
   opAt 3037 (.Dup ⟨2, by decide⟩),
   opAt 3038 .MSTORE,
   opAt 3039 (.Swap ⟨0, by decide⟩),
   opAt 3040 (.Swap ⟨1, by decide⟩),
   opAt 3041 .OR,
   opAt 3042 (.Swap ⟨0, by decide⟩),
   pushAt 3043 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3044 .ADD,
   pushAt 3045 2 8255,
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 .GT,
   pushAt 3048 2 5135,
   opAt 3049 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3050 .POP,
   pushAt 3051 2 8224,
   opAt 3052 .MLOAD,
   opAt 3053 (.Dup ⟨1, by decide⟩),
   opAt 3054 .ADD,
   opAt 3055 (.Dup ⟨0, by decide⟩),
   pushAt 3056 2 8224,
   opAt 3057 .MSTORE,
   opAt 3058 .LT,
   opAt 3059 .ISZERO,
   pushAt 3060 2 5129,
   opAt 3061 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3062 .JUMPDEST,
   pushAt 3063 2 8224,
   opAt 3064 .MLOAD,
   opAt 3065 .ISZERO,
   pushAt 3066 2 5325,
   opAt 3067 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3068 0 0,
   pushAt 3069 2 9440,
   opAt 3070 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3071 .JUMPDEST,
   opAt 3072 (.Dup ⟨0, by decide⟩),
   opAt 3073 .MLOAD,
   opAt 3074 (.Dup ⟨1, by decide⟩),
   pushAt 3075 2 8256,
   opAt 3076 (.Swap ⟨0, by decide⟩),
   opAt 3077 .SUB,
   opAt 3078 .MLOAD,
   opAt 3079 (.Dup ⟨1, by decide⟩),
   opAt 3080 (.Dup ⟨1, by decide⟩),
   opAt 3081 .GT,
   opAt 3082 (.Swap ⟨1, by decide⟩),
   opAt 3083 .SUB,
   opAt 3084 (.Dup ⟨3, by decide⟩),
   opAt 3085 (.Dup ⟨1, by decide⟩),
   opAt 3086 .LT,
   opAt 3087 (.Swap ⟨0, by decide⟩),
   opAt 3088 (.Dup ⟨4, by decide⟩),
   opAt 3089 (.Swap ⟨0, by decide⟩),
   opAt 3090 .SUB,
   opAt 3091 (.Dup ⟨3, by decide⟩),
   opAt 3092 .MSTORE,
   opAt 3093 .OR,
   opAt 3094 (.Swap ⟨1, by decide⟩),
   opAt 3095 .POP,
   pushAt 3096 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3097 .ADD,
   pushAt 3098 2 8255,
   opAt 3099 (.Dup ⟨1, by decide⟩),
   opAt 3100 .GT,
   pushAt 3101 2 5241,
   opAt 3102 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3103 .POP,
   pushAt 3104 2 8224,
   opAt 3105 .MLOAD,
   opAt 3106 .SUB,
   pushAt 3107 2 8224,
   opAt 3108 .MSTORE,
   pushAt 3109 2 5226,
   opAt 3110 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3111 .JUMPDEST,
   pushAt 3112 2 5336,
   pushAt 3113 2 2048,
   pushAt 3114 2 2637,
   opAt 3115 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3116 .JUMPDEST,
   pushAt 3117 1 1,
   opAt 3118 (.Swap ⟨0, by decide⟩),
   opAt 3119 .SUB,
   pushAt 3120 2 4849,
   opAt 3121 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3122 .JUMPDEST,
   opAt 3123 .POP,
   pushAt 3124 2 1756,
   opAt 3125 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4618 = true :=
  Artifact.isValidJumpDest_index 2718 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4662 = true :=
  Artifact.isValidJumpDest_index 2745 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4667 = true :=
  Artifact.isValidJumpDest_index 2748 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4674 = true :=
  Artifact.isValidJumpDest_index 2752 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 2775 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4781 = true :=
  Artifact.isValidJumpDest_index 2812 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4812 = true :=
  Artifact.isValidJumpDest_index 2838 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4849 = true :=
  Artifact.isValidJumpDest_index 2869 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4870 = true :=
  Artifact.isValidJumpDest_index 2882 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4938 = true :=
  Artifact.isValidJumpDest_index 2932 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4952 = true :=
  Artifact.isValidJumpDest_index 2940 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5129 = true :=
  Artifact.isValidJumpDest_index 3011 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5135 = true :=
  Artifact.isValidJumpDest_index 3015 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5226 = true :=
  Artifact.isValidJumpDest_index 3062 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5241 = true :=
  Artifact.isValidJumpDest_index 3071 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5325 = true :=
  Artifact.isValidJumpDest_index 3111 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5336 = true :=
  Artifact.isValidJumpDest_index 3116 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5345 = true :=
  Artifact.isValidJumpDest_index 3122 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
