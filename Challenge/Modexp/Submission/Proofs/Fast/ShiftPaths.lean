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
  [opAt 2710 .JUMPDEST,
   opAt 2711 (.Dup ⟨0, by decide⟩),
   opAt 2712 (.Dup ⟨3, by decide⟩),
   opAt 2713 .EQ,
   pushAt 2714 0 0,
   opAt 2715 .MLOAD,
   pushAt 2716 1 255,
   opAt 2717 .SHR,
   opAt 2718 .AND,
   opAt 2719 .ISZERO,
   pushAt 2720 2 4662,
   opAt 2721 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2722 (.Dup ⟨0, by decide⟩),
   pushAt 2723 1 96,
   pushAt 2724 2 1024,
   opAt 2725 .CALLDATACOPY,
   opAt 2726 (.Dup ⟨0, by decide⟩),
   pushAt 2727 1 96,
   pushAt 2728 2 8256,
   opAt 2729 .CALLDATACOPY,
   pushAt 2730 0 0,
   pushAt 2731 2 8224,
   opAt 2732 .MSTORE,
   pushAt 2733 2 4667,
   pushAt 2734 2 2048,
   pushAt 2735 2 2637,
   opAt 2736 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2737 .JUMPDEST,
   pushAt 2738 2 1533,
   opAt 2739 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2740 .JUMPDEST,
   pushAt 2741 1 1,
   pushAt 2742 2 9408,
   opAt 2743 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2744 .JUMPDEST,
   opAt 2745 (.Dup ⟨0, by decide⟩),
   opAt 2746 .MLOAD,
   opAt 2747 .NOT,
   opAt 2748 (.Dup ⟨2, by decide⟩),
   opAt 2749 .ADD,
   opAt 2750 (.Dup ⟨2, by decide⟩),
   opAt 2751 (.Dup ⟨1, by decide⟩),
   opAt 2752 .LT,
   opAt 2753 (.Swap ⟨2, by decide⟩),
   opAt 2754 .POP,
   opAt 2755 (.Dup ⟨1, by decide⟩),
   pushAt 2756 2 5120,
   opAt 2757 .ADD,
   opAt 2758 .MSTORE,
   opAt 2759 (.Dup ⟨0, by decide⟩),
   opAt 2760 .ISZERO,
   pushAt 2761 2 4735,
   opAt 2762 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2763 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2764 .ADD,
   pushAt 2765 2 4674,
   opAt 2766 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2767 .JUMPDEST,
   opAt 2768 .POP,
   opAt 2769 .POP,
   pushAt 2770 0 0,
   opAt 2771 .MLOAD,
   opAt 2772 (.Dup ⟨0, by decide⟩),
   pushAt 2773 0 0,
   opAt 2774 .SUB,
   opAt 2775 (.Dup ⟨1, by decide⟩),
   opAt 2776 .AND,
   opAt 2777 (.Dup ⟨0, by decide⟩),
   pushAt 2778 2 6144,
   opAt 2779 .MSTORE,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   opAt 2781 (.Dup ⟨2, by decide⟩),
   opAt 2782 .DIV,
   opAt 2783 (.Dup ⟨0, by decide⟩),
   pushAt 2784 2 6176,
   opAt 2785 .MSTORE,
   opAt 2786 (.Dup ⟨1, by decide⟩),
   pushAt 2787 0 0,
   opAt 2788 .SUB,
   opAt 2789 (.Dup ⟨2, by decide⟩),
   opAt 2790 (.Swap ⟨0, by decide⟩),
   opAt 2791 .DIV,
   pushAt 2792 1 1,
   opAt 2793 .ADD,
   pushAt 2794 2 6208,
   opAt 2795 .MSTORE,
   opAt 2796 (.Dup ⟨0, by decide⟩),
   pushAt 2797 0 0,
   opAt 2798 .SUB,
   opAt 2799 (.Dup ⟨1, by decide⟩),
   opAt 2800 (.Swap ⟨0, by decide⟩),
   opAt 2801 .MOD,
   pushAt 2802 2 6240,
   opAt 2803 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2804 .JUMPDEST,
   pushAt 2805 1 1,
   opAt 2806 (.Dup ⟨0, by decide⟩),
   opAt 2807 (.Dup ⟨2, by decide⟩),
   opAt 2808 .MUL,
   pushAt 2809 1 2,
   opAt 2810 .SUB,
   opAt 2811 .MUL,
   opAt 2812 (.Dup ⟨0, by decide⟩),
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 .MUL,
   pushAt 2815 1 2,
   opAt 2816 .SUB,
   opAt 2817 .MUL,
   opAt 2818 (.Dup ⟨0, by decide⟩),
   opAt 2819 (.Dup ⟨2, by decide⟩),
   opAt 2820 .MUL,
   pushAt 2821 1 2,
   opAt 2822 .SUB,
   opAt 2823 .MUL,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   opAt 2825 (.Dup ⟨2, by decide⟩),
   opAt 2826 .MUL,
   pushAt 2827 1 2,
   opAt 2828 .SUB,
   opAt 2829 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2830 .JUMPDEST,
   opAt 2831 (.Dup ⟨0, by decide⟩),
   opAt 2832 (.Dup ⟨2, by decide⟩),
   opAt 2833 .MUL,
   pushAt 2834 1 2,
   opAt 2835 .SUB,
   opAt 2836 .MUL,
   opAt 2837 (.Dup ⟨0, by decide⟩),
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
   pushAt 2855 2 6272,
   opAt 2856 .MSTORE,
   opAt 2857 .POP,
   opAt 2858 .POP,
   opAt 2859 .POP,
   opAt 2860 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2861 .JUMPDEST,
   opAt 2862 (.Dup ⟨0, by decide⟩),
   opAt 2863 .ISZERO,
   pushAt 2864 2 5345,
   opAt 2865 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2866 (.Dup ⟨1, by decide⟩),
   pushAt 2867 2 2048,
   pushAt 2868 2 8224,
   opAt 2869 .MCOPY,
   pushAt 2870 0 0,
   pushAt 2871 2 9440,
   opAt 2872 .MLOAD,
   opAt 2873 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2874 .JUMPDEST,
   pushAt 2875 2 2048,
   opAt 2876 .MLOAD,
   pushAt 2877 2 6144,
   opAt 2878 .MLOAD,
   opAt 2879 (.Dup ⟨1, by decide⟩),
   opAt 2880 (.Dup ⟨1, by decide⟩),
   opAt 2881 (.Swap ⟨0, by decide⟩),
   opAt 2882 .DIV,
   opAt 2883 (.Swap ⟨1, by decide⟩),
   opAt 2884 .MOD,
   pushAt 2885 2 6208,
   opAt 2886 .MLOAD,
   opAt 2887 .MUL,
   pushAt 2888 2 2080,
   opAt 2889 .MLOAD,
   pushAt 2890 2 6144,
   opAt 2891 .MLOAD,
   opAt 2892 (.Swap ⟨0, by decide⟩),
   opAt 2893 .DIV,
   opAt 2894 .ADD,
   pushAt 2895 2 6176,
   opAt 2896 .MLOAD,
   opAt 2897 (.Dup ⟨0, by decide⟩),
   pushAt 2898 2 6240,
   opAt 2899 .MLOAD,
   opAt 2900 (.Dup ⟨4, by decide⟩),
   opAt 2901 .MULMOD,
   opAt 2902 (.Dup ⟨2, by decide⟩),
   opAt 2903 (.Swap ⟨0, by decide⟩),
   opAt 2904 .ADDMOD,
   opAt 2905 (.Swap ⟨0, by decide⟩),
   opAt 2906 .SUB,
   pushAt 2907 2 6272,
   opAt 2908 .MLOAD,
   opAt 2909 .MUL,
   opAt 2910 (.Dup ⟨0, by decide⟩),
   opAt 2911 .ISZERO,
   opAt 2912 .ISZERO,
   opAt 2913 (.Swap ⟨0, by decide⟩),
   opAt 2914 .SUB,
   opAt 2915 (.Swap ⟨0, by decide⟩),
   pushAt 2916 2 6176,
   opAt 2917 .MLOAD,
   opAt 2918 (.Swap ⟨0, by decide⟩),
   opAt 2919 .LT,
   opAt 2920 .ISZERO,
   pushAt 2921 0 0,
   opAt 2922 .SUB,
   opAt 2923 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2924 .JUMPDEST,
   pushAt 2925 0 0,
   pushAt 2926 2 9440,
   opAt 2927 .MLOAD,
   pushAt 2928 2 9408,
   opAt 2929 .MLOAD,
   pushAt 2930 2 5120,
   opAt 2931 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2932 .JUMPDEST,
   opAt 2933 (.Dup ⟨0, by decide⟩),
   opAt 2934 .MLOAD,
   pushAt 2935 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2936 (.Dup ⟨5, by decide⟩),
   opAt 2937 (.Dup ⟨2, by decide⟩),
   opAt 2938 .MUL,
   opAt 2939 (.Swap ⟨1, by decide⟩),
   opAt 2940 (.Dup ⟨6, by decide⟩),
   opAt 2941 .MULMOD,
   opAt 2942 (.Dup ⟨1, by decide⟩),
   opAt 2943 (.Dup ⟨1, by decide⟩),
   opAt 2944 .LT,
   opAt 2945 .SUB,
   opAt 2946 (.Dup ⟨4, by decide⟩),
   opAt 2947 (.Dup ⟨2, by decide⟩),
   opAt 2948 .ADD,
   opAt 2949 (.Dup ⟨0, by decide⟩),
   opAt 2950 (.Swap ⟨5, by decide⟩),
   opAt 2951 .GT,
   opAt 2952 .SUB,
   opAt 2953 .SUB,
   opAt 2954 (.Dup ⟨3, by decide⟩),
   opAt 2955 (.Dup ⟨3, by decide⟩),
   opAt 2956 .MLOAD,
   opAt 2957 .ADD,
   opAt 2958 (.Dup ⟨0, by decide⟩),
   opAt 2959 (.Swap ⟨4, by decide⟩),
   opAt 2960 .GT,
   opAt 2961 .ADD,
   opAt 2962 (.Swap ⟨2, by decide⟩),
   opAt 2963 (.Dup ⟨2, by decide⟩),
   pushAt 2964 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2965 .ADD,
   opAt 2966 (.Swap ⟨2, by decide⟩),
   opAt 2967 .MSTORE,
   pushAt 2968 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2969 .ADD,
   pushAt 2970 2 8224,
   opAt 2971 (.Dup ⟨2, by decide⟩),
   opAt 2972 .GT,
   pushAt 2973 2 4952,
   opAt 2974 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2975 .POP,
   opAt 2976 .POP,
   pushAt 2977 2 8224,
   opAt 2978 .MLOAD,
   opAt 2979 (.Dup ⟨1, by decide⟩),
   opAt 2980 .ADD,
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 (.Dup ⟨1, by decide⟩),
   opAt 2983 .LT,
   opAt 2984 (.Swap ⟨1, by decide⟩),
   opAt 2985 .POP,
   opAt 2986 (.Dup ⟨2, by decide⟩),
   opAt 2987 (.Dup ⟨1, by decide⟩),
   opAt 2988 .LT,
   opAt 2989 (.Swap ⟨0, by decide⟩),
   opAt 2990 (.Dup ⟨3, by decide⟩),
   opAt 2991 (.Swap ⟨0, by decide⟩),
   opAt 2992 .SUB,
   opAt 2993 (.Dup ⟨0, by decide⟩),
   pushAt 2994 2 8224,
   opAt 2995 .MSTORE,
   opAt 2996 .POP,
   opAt 2997 .GT,
   opAt 2998 (.Swap ⟨0, by decide⟩),
   opAt 2999 .POP,
   opAt 3000 .ISZERO,
   pushAt 3001 2 5226,
   opAt 3002 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3003 .JUMPDEST,
   pushAt 3004 0 0,
   pushAt 3005 2 9440,
   opAt 3006 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3007 .JUMPDEST,
   opAt 3008 (.Dup ⟨0, by decide⟩),
   opAt 3009 .MLOAD,
   opAt 3010 (.Dup ⟨1, by decide⟩),
   pushAt 3011 2 8256,
   opAt 3012 (.Swap ⟨0, by decide⟩),
   opAt 3013 .SUB,
   opAt 3014 .MLOAD,
   opAt 3015 (.Dup ⟨1, by decide⟩),
   opAt 3016 .ADD,
   opAt 3017 (.Dup ⟨0, by decide⟩),
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .GT,
   opAt 3020 (.Swap ⟨1, by decide⟩),
   opAt 3021 .POP,
   opAt 3022 (.Dup ⟨3, by decide⟩),
   opAt 3023 .ADD,
   opAt 3024 (.Dup ⟨0, by decide⟩),
   opAt 3025 (.Dup ⟨4, by decide⟩),
   opAt 3026 .GT,
   opAt 3027 (.Swap ⟨3, by decide⟩),
   opAt 3028 .POP,
   opAt 3029 (.Dup ⟨2, by decide⟩),
   opAt 3030 .MSTORE,
   opAt 3031 (.Swap ⟨0, by decide⟩),
   opAt 3032 (.Swap ⟨1, by decide⟩),
   opAt 3033 .OR,
   opAt 3034 (.Swap ⟨0, by decide⟩),
   pushAt 3035 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3036 .ADD,
   pushAt 3037 2 8255,
   opAt 3038 (.Dup ⟨1, by decide⟩),
   opAt 3039 .GT,
   pushAt 3040 2 5135,
   opAt 3041 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3042 .POP,
   pushAt 3043 2 8224,
   opAt 3044 .MLOAD,
   opAt 3045 (.Dup ⟨1, by decide⟩),
   opAt 3046 .ADD,
   opAt 3047 (.Dup ⟨0, by decide⟩),
   pushAt 3048 2 8224,
   opAt 3049 .MSTORE,
   opAt 3050 .LT,
   opAt 3051 .ISZERO,
   pushAt 3052 2 5129,
   opAt 3053 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3054 .JUMPDEST,
   pushAt 3055 2 8224,
   opAt 3056 .MLOAD,
   opAt 3057 .ISZERO,
   pushAt 3058 2 5325,
   opAt 3059 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3060 0 0,
   pushAt 3061 2 9440,
   opAt 3062 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3063 .JUMPDEST,
   opAt 3064 (.Dup ⟨0, by decide⟩),
   opAt 3065 .MLOAD,
   opAt 3066 (.Dup ⟨1, by decide⟩),
   pushAt 3067 2 8256,
   opAt 3068 (.Swap ⟨0, by decide⟩),
   opAt 3069 .SUB,
   opAt 3070 .MLOAD,
   opAt 3071 (.Dup ⟨1, by decide⟩),
   opAt 3072 (.Dup ⟨1, by decide⟩),
   opAt 3073 .GT,
   opAt 3074 (.Swap ⟨1, by decide⟩),
   opAt 3075 .SUB,
   opAt 3076 (.Dup ⟨3, by decide⟩),
   opAt 3077 (.Dup ⟨1, by decide⟩),
   opAt 3078 .LT,
   opAt 3079 (.Swap ⟨0, by decide⟩),
   opAt 3080 (.Dup ⟨4, by decide⟩),
   opAt 3081 (.Swap ⟨0, by decide⟩),
   opAt 3082 .SUB,
   opAt 3083 (.Dup ⟨3, by decide⟩),
   opAt 3084 .MSTORE,
   opAt 3085 .OR,
   opAt 3086 (.Swap ⟨1, by decide⟩),
   opAt 3087 .POP,
   pushAt 3088 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3089 .ADD,
   pushAt 3090 2 8255,
   opAt 3091 (.Dup ⟨1, by decide⟩),
   opAt 3092 .GT,
   pushAt 3093 2 5241,
   opAt 3094 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3095 .POP,
   pushAt 3096 2 8224,
   opAt 3097 .MLOAD,
   opAt 3098 .SUB,
   pushAt 3099 2 8224,
   opAt 3100 .MSTORE,
   pushAt 3101 2 5226,
   opAt 3102 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3103 .JUMPDEST,
   pushAt 3104 2 5336,
   pushAt 3105 2 2048,
   pushAt 3106 2 2637,
   opAt 3107 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3108 .JUMPDEST,
   pushAt 3109 1 1,
   opAt 3110 (.Swap ⟨0, by decide⟩),
   opAt 3111 .SUB,
   pushAt 3112 2 4849,
   opAt 3113 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3114 .JUMPDEST,
   opAt 3115 .POP,
   pushAt 3116 2 1756,
   opAt 3117 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4618 = true :=
  Artifact.isValidJumpDest_index 2710 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4662 = true :=
  Artifact.isValidJumpDest_index 2737 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4667 = true :=
  Artifact.isValidJumpDest_index 2740 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4674 = true :=
  Artifact.isValidJumpDest_index 2744 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 2767 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4781 = true :=
  Artifact.isValidJumpDest_index 2804 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4812 = true :=
  Artifact.isValidJumpDest_index 2830 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4849 = true :=
  Artifact.isValidJumpDest_index 2861 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4870 = true :=
  Artifact.isValidJumpDest_index 2874 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4938 = true :=
  Artifact.isValidJumpDest_index 2924 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4952 = true :=
  Artifact.isValidJumpDest_index 2932 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5129 = true :=
  Artifact.isValidJumpDest_index 3003 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5135 = true :=
  Artifact.isValidJumpDest_index 3007 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5226 = true :=
  Artifact.isValidJumpDest_index 3054 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5241 = true :=
  Artifact.isValidJumpDest_index 3063 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5325 = true :=
  Artifact.isValidJumpDest_index 3103 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5336 = true :=
  Artifact.isValidJumpDest_index 3108 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5345 = true :=
  Artifact.isValidJumpDest_index 3114 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
