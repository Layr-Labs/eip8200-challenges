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
   pushAt 2872 2 5344,
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
   opAt 2926 .GT,
   opAt 2927 .ISZERO,
   pushAt 2928 0 0,
   opAt 2929 .SUB,
   opAt 2930 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2931 .JUMPDEST,
   pushAt 2932 0 0,
   pushAt 2933 2 9440,
   opAt 2934 .MLOAD,
   pushAt 2935 2 9408,
   opAt 2936 .MLOAD,
   pushAt 2937 2 5120,
   opAt 2938 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2939 .JUMPDEST,
   opAt 2940 (.Dup ⟨0, by decide⟩),
   opAt 2941 .MLOAD,
   pushAt 2942 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2943 (.Dup ⟨5, by decide⟩),
   opAt 2944 (.Dup ⟨2, by decide⟩),
   opAt 2945 .MUL,
   opAt 2946 (.Swap ⟨1, by decide⟩),
   opAt 2947 (.Dup ⟨6, by decide⟩),
   opAt 2948 .MULMOD,
   opAt 2949 (.Dup ⟨1, by decide⟩),
   opAt 2950 (.Dup ⟨1, by decide⟩),
   opAt 2951 .LT,
   opAt 2952 .SUB,
   opAt 2953 (.Dup ⟨4, by decide⟩),
   opAt 2954 (.Dup ⟨2, by decide⟩),
   opAt 2955 .ADD,
   opAt 2956 (.Dup ⟨0, by decide⟩),
   opAt 2957 (.Swap ⟨5, by decide⟩),
   opAt 2958 .GT,
   opAt 2959 .SUB,
   opAt 2960 .SUB,
   opAt 2961 (.Dup ⟨3, by decide⟩),
   opAt 2962 (.Dup ⟨3, by decide⟩),
   opAt 2963 .MLOAD,
   opAt 2964 .ADD,
   opAt 2965 (.Dup ⟨0, by decide⟩),
   opAt 2966 (.Swap ⟨4, by decide⟩),
   opAt 2967 .GT,
   opAt 2968 .ADD,
   opAt 2969 (.Swap ⟨2, by decide⟩),
   opAt 2970 (.Dup ⟨2, by decide⟩),
   pushAt 2971 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2972 .ADD,
   opAt 2973 (.Swap ⟨2, by decide⟩),
   opAt 2974 .MSTORE,
   pushAt 2975 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2976 .ADD,
   pushAt 2977 2 8224,
   opAt 2978 (.Dup ⟨2, by decide⟩),
   opAt 2979 .GT,
   pushAt 2980 2 4951,
   opAt 2981 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2982 .POP,
   opAt 2983 .POP,
   pushAt 2984 2 8224,
   opAt 2985 .MLOAD,
   opAt 2986 (.Dup ⟨1, by decide⟩),
   opAt 2987 .ADD,
   opAt 2988 (.Dup ⟨1, by decide⟩),
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 .LT,
   opAt 2991 (.Swap ⟨1, by decide⟩),
   opAt 2992 .POP,
   opAt 2993 (.Dup ⟨2, by decide⟩),
   opAt 2994 (.Dup ⟨1, by decide⟩),
   opAt 2995 .LT,
   opAt 2996 (.Swap ⟨0, by decide⟩),
   opAt 2997 (.Dup ⟨3, by decide⟩),
   opAt 2998 (.Swap ⟨0, by decide⟩),
   opAt 2999 .SUB,
   opAt 3000 (.Dup ⟨0, by decide⟩),
   pushAt 3001 2 8224,
   opAt 3002 .MSTORE,
   opAt 3003 .POP,
   opAt 3004 .GT,
   opAt 3005 (.Swap ⟨0, by decide⟩),
   opAt 3006 .POP,
   opAt 3007 .ISZERO,
   pushAt 3008 2 5225,
   opAt 3009 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3010 .JUMPDEST,
   pushAt 3011 0 0,
   pushAt 3012 2 9440,
   opAt 3013 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3014 .JUMPDEST,
   opAt 3015 (.Dup ⟨0, by decide⟩),
   opAt 3016 .MLOAD,
   opAt 3017 (.Dup ⟨1, by decide⟩),
   pushAt 3018 2 8256,
   opAt 3019 (.Swap ⟨0, by decide⟩),
   opAt 3020 .SUB,
   opAt 3021 .MLOAD,
   opAt 3022 (.Dup ⟨1, by decide⟩),
   opAt 3023 .ADD,
   opAt 3024 (.Dup ⟨0, by decide⟩),
   opAt 3025 (.Dup ⟨2, by decide⟩),
   opAt 3026 .GT,
   opAt 3027 (.Swap ⟨1, by decide⟩),
   opAt 3028 .POP,
   opAt 3029 (.Dup ⟨3, by decide⟩),
   opAt 3030 .ADD,
   opAt 3031 (.Dup ⟨0, by decide⟩),
   opAt 3032 (.Dup ⟨4, by decide⟩),
   opAt 3033 .GT,
   opAt 3034 (.Swap ⟨3, by decide⟩),
   opAt 3035 .POP,
   opAt 3036 (.Dup ⟨2, by decide⟩),
   opAt 3037 .MSTORE,
   opAt 3038 (.Swap ⟨0, by decide⟩),
   opAt 3039 (.Swap ⟨1, by decide⟩),
   opAt 3040 .OR,
   opAt 3041 (.Swap ⟨0, by decide⟩),
   pushAt 3042 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3043 .ADD,
   pushAt 3044 2 8255,
   opAt 3045 (.Dup ⟨1, by decide⟩),
   opAt 3046 .GT,
   pushAt 3047 2 5134,
   opAt 3048 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3049 .POP,
   pushAt 3050 2 8224,
   opAt 3051 .MLOAD,
   opAt 3052 (.Dup ⟨1, by decide⟩),
   opAt 3053 .ADD,
   opAt 3054 (.Dup ⟨0, by decide⟩),
   pushAt 3055 2 8224,
   opAt 3056 .MSTORE,
   opAt 3057 .LT,
   opAt 3058 .ISZERO,
   pushAt 3059 2 5128,
   opAt 3060 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3061 .JUMPDEST,
   pushAt 3062 2 8224,
   opAt 3063 .MLOAD,
   opAt 3064 .ISZERO,
   pushAt 3065 2 5324,
   opAt 3066 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3067 0 0,
   pushAt 3068 2 9440,
   opAt 3069 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3070 .JUMPDEST,
   opAt 3071 (.Dup ⟨0, by decide⟩),
   opAt 3072 .MLOAD,
   opAt 3073 (.Dup ⟨1, by decide⟩),
   pushAt 3074 2 8256,
   opAt 3075 (.Swap ⟨0, by decide⟩),
   opAt 3076 .SUB,
   opAt 3077 .MLOAD,
   opAt 3078 (.Dup ⟨1, by decide⟩),
   opAt 3079 (.Dup ⟨1, by decide⟩),
   opAt 3080 .GT,
   opAt 3081 (.Swap ⟨1, by decide⟩),
   opAt 3082 .SUB,
   opAt 3083 (.Dup ⟨3, by decide⟩),
   opAt 3084 (.Dup ⟨1, by decide⟩),
   opAt 3085 .LT,
   opAt 3086 (.Swap ⟨0, by decide⟩),
   opAt 3087 (.Dup ⟨4, by decide⟩),
   opAt 3088 (.Swap ⟨0, by decide⟩),
   opAt 3089 .SUB,
   opAt 3090 (.Dup ⟨3, by decide⟩),
   opAt 3091 .MSTORE,
   opAt 3092 .OR,
   opAt 3093 (.Swap ⟨1, by decide⟩),
   opAt 3094 .POP,
   pushAt 3095 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3096 .ADD,
   pushAt 3097 2 8255,
   opAt 3098 (.Dup ⟨1, by decide⟩),
   opAt 3099 .GT,
   pushAt 3100 2 5240,
   opAt 3101 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3102 .POP,
   pushAt 3103 2 8224,
   opAt 3104 .MLOAD,
   opAt 3105 .SUB,
   pushAt 3106 2 8224,
   opAt 3107 .MSTORE,
   pushAt 3108 2 5225,
   opAt 3109 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 .JUMPDEST,
   pushAt 3111 2 5335,
   pushAt 3112 2 2048,
   pushAt 3113 2 2637,
   opAt 3114 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3115 .JUMPDEST,
   pushAt 3116 1 1,
   opAt 3117 (.Swap ⟨0, by decide⟩),
   opAt 3118 .SUB,
   pushAt 3119 2 4849,
   opAt 3120 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3121 .JUMPDEST,
   opAt 3122 .POP,
   pushAt 3123 2 1756,
   opAt 3124 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4937 = true :=
  Artifact.isValidJumpDest_index 2931 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4951 = true :=
  Artifact.isValidJumpDest_index 2939 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5128 = true :=
  Artifact.isValidJumpDest_index 3010 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5134 = true :=
  Artifact.isValidJumpDest_index 3014 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5225 = true :=
  Artifact.isValidJumpDest_index 3061 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5240 = true :=
  Artifact.isValidJumpDest_index 3070 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5324 = true :=
  Artifact.isValidJumpDest_index 3110 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5335 = true :=
  Artifact.isValidJumpDest_index 3115 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5344 = true :=
  Artifact.isValidJumpDest_index 3121 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
