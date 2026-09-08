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
  [opAt 2695 .JUMPDEST,
   opAt 2696 (.Dup ⟨0, by decide⟩),
   opAt 2697 (.Dup ⟨3, by decide⟩),
   opAt 2698 .EQ,
   pushAt 2699 0 0,
   opAt 2700 .MLOAD,
   pushAt 2701 1 255,
   opAt 2702 .SHR,
   opAt 2703 .AND,
   opAt 2704 .ISZERO,
   pushAt 2705 2 4092,
   opAt 2706 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2707 (.Dup ⟨0, by decide⟩),
   pushAt 2708 1 96,
   pushAt 2709 2 1024,
   opAt 2710 .CALLDATACOPY,
   opAt 2711 (.Dup ⟨0, by decide⟩),
   pushAt 2712 1 96,
   pushAt 2713 2 8256,
   opAt 2714 .CALLDATACOPY,
   pushAt 2715 0 0,
   pushAt 2716 2 8224,
   opAt 2717 .MSTORE,
   pushAt 2718 2 4097,
   pushAt 2719 2 2048,
   pushAt 2720 2 2517,
   opAt 2721 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2722 .JUMPDEST,
   pushAt 2723 2 1533,
   opAt 2724 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2725 .JUMPDEST,
   pushAt 2726 1 1,
   pushAt 2727 2 9408,
   opAt 2728 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2729 .JUMPDEST,
   opAt 2730 (.Dup ⟨0, by decide⟩),
   opAt 2731 .MLOAD,
   opAt 2732 .NOT,
   opAt 2733 (.Dup ⟨2, by decide⟩),
   opAt 2734 .ADD,
   opAt 2735 (.Dup ⟨2, by decide⟩),
   opAt 2736 (.Dup ⟨1, by decide⟩),
   opAt 2737 .LT,
   opAt 2738 (.Swap ⟨2, by decide⟩),
   opAt 2739 .POP,
   opAt 2740 (.Dup ⟨1, by decide⟩),
   pushAt 2741 2 5120,
   opAt 2742 .ADD,
   opAt 2743 .MSTORE,
   opAt 2744 (.Dup ⟨0, by decide⟩),
   opAt 2745 .ISZERO,
   pushAt 2746 2 4135,
   opAt 2747 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2748 1 31, opAt 2749 .NOT,
   opAt 2750 .ADD,
   pushAt 2751 2 4104,
   opAt 2752 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2753 .JUMPDEST,
   opAt 2754 .POP,
   opAt 2755 .POP,
   pushAt 2756 0 0,
   opAt 2757 .MLOAD,
   opAt 2758 (.Dup ⟨0, by decide⟩),
   pushAt 2759 0 0,
   opAt 2760 .SUB,
   opAt 2761 (.Dup ⟨1, by decide⟩),
   opAt 2762 .AND,
   opAt 2763 (.Dup ⟨0, by decide⟩),
   pushAt 2764 2 6144,
   opAt 2765 .MSTORE,
   opAt 2766 (.Dup ⟨0, by decide⟩),
   opAt 2767 (.Dup ⟨2, by decide⟩),
   opAt 2768 .DIV,
   opAt 2769 (.Dup ⟨0, by decide⟩),
   pushAt 2770 2 6176,
   opAt 2771 .MSTORE,
   opAt 2772 (.Dup ⟨1, by decide⟩),
   pushAt 2773 0 0,
   opAt 2774 .SUB,
   opAt 2775 (.Dup ⟨2, by decide⟩),
   opAt 2776 (.Swap ⟨0, by decide⟩),
   opAt 2777 .DIV,
   pushAt 2778 1 1,
   opAt 2779 .ADD,
   pushAt 2780 2 6208,
   opAt 2781 .MSTORE,
   opAt 2782 (.Dup ⟨0, by decide⟩),
   pushAt 2783 0 0,
   opAt 2784 .SUB,
   opAt 2785 (.Dup ⟨1, by decide⟩),
   opAt 2786 (.Swap ⟨0, by decide⟩),
   opAt 2787 .MOD,
   pushAt 2788 2 6240,
   opAt 2789 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2790 .JUMPDEST,
   pushAt 2791 1 1,
   opAt 2792 (.Dup ⟨0, by decide⟩),
   opAt 2793 (.Dup ⟨2, by decide⟩),
   opAt 2794 .MUL,
   pushAt 2795 1 2,
   opAt 2796 .SUB,
   opAt 2797 .MUL,
   opAt 2798 (.Dup ⟨0, by decide⟩),
   opAt 2799 (.Dup ⟨2, by decide⟩),
   opAt 2800 .MUL,
   pushAt 2801 1 2,
   opAt 2802 .SUB,
   opAt 2803 .MUL,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   opAt 2805 (.Dup ⟨2, by decide⟩),
   opAt 2806 .MUL,
   pushAt 2807 1 2,
   opAt 2808 .SUB,
   opAt 2809 .MUL,
   opAt 2810 (.Dup ⟨0, by decide⟩),
   opAt 2811 (.Dup ⟨2, by decide⟩),
   opAt 2812 .MUL,
   pushAt 2813 1 2,
   opAt 2814 .SUB,
   opAt 2815 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2816 .JUMPDEST,
   opAt 2817 (.Dup ⟨0, by decide⟩),
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .MUL,
   pushAt 2820 1 2,
   opAt 2821 .SUB,
   opAt 2822 .MUL,
   opAt 2823 (.Dup ⟨0, by decide⟩),
   opAt 2824 (.Dup ⟨2, by decide⟩),
   opAt 2825 .MUL,
   pushAt 2826 1 2,
   opAt 2827 .SUB,
   opAt 2828 .MUL,
   opAt 2829 (.Dup ⟨0, by decide⟩),
   opAt 2830 (.Dup ⟨2, by decide⟩),
   opAt 2831 .MUL,
   pushAt 2832 1 2,
   opAt 2833 .SUB,
   opAt 2834 .MUL,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   opAt 2836 (.Dup ⟨2, by decide⟩),
   opAt 2837 .MUL,
   pushAt 2838 1 2,
   opAt 2839 .SUB,
   opAt 2840 .MUL,
   pushAt 2841 2 6272,
   opAt 2842 .MSTORE,
   opAt 2843 .POP,
   opAt 2844 .POP,
   opAt 2845 .POP,
   opAt 2846 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2847 .JUMPDEST,
   opAt 2848 (.Dup ⟨0, by decide⟩),
   opAt 2849 .ISZERO,
   pushAt 2850 2 4595,
   opAt 2851 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2852 (.Dup ⟨1, by decide⟩),
   pushAt 2853 2 2048,
   pushAt 2854 2 8224,
   opAt 2855 .MCOPY,
   pushAt 2856 0 0,
   pushAt 2857 2 9440,
   opAt 2858 .MLOAD,
   opAt 2859 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2860 .JUMPDEST,
   pushAt 2861 2 2048,
   opAt 2862 .MLOAD,
   pushAt 2863 2 6144,
   opAt 2864 .MLOAD,
   opAt 2865 (.Dup ⟨1, by decide⟩),
   opAt 2866 (.Dup ⟨1, by decide⟩),
   opAt 2867 (.Swap ⟨0, by decide⟩),
   opAt 2868 .DIV,
   opAt 2869 (.Swap ⟨1, by decide⟩),
   opAt 2870 .MOD,
   pushAt 2871 2 6208,
   opAt 2872 .MLOAD,
   opAt 2873 .MUL,
   pushAt 2874 2 2080,
   opAt 2875 .MLOAD,
   pushAt 2876 2 6144,
   opAt 2877 .MLOAD,
   opAt 2878 (.Swap ⟨0, by decide⟩),
   opAt 2879 .DIV,
   opAt 2880 .ADD,
   pushAt 2881 2 6176,
   opAt 2882 .MLOAD,
   opAt 2883 (.Dup ⟨0, by decide⟩),
   pushAt 2884 2 6240,
   opAt 2885 .MLOAD,
   opAt 2886 (.Dup ⟨4, by decide⟩),
   opAt 2887 .MULMOD,
   opAt 2888 (.Dup ⟨2, by decide⟩),
   opAt 2889 .JUMPDEST,
   opAt 2890 .ADDMOD,
   opAt 2891 (.Swap ⟨0, by decide⟩),
   opAt 2892 .SUB,
   pushAt 2893 2 6272,
   opAt 2894 .MLOAD,
   opAt 2895 .MUL,
   opAt 2896 (.Dup ⟨0, by decide⟩),
   pushAt 2897 0 0,
   opAt 2898 .LT,
   opAt 2899 (.Swap ⟨0, by decide⟩),
   opAt 2900 .SUB,
   opAt 2901 (.Swap ⟨0, by decide⟩),
   pushAt 2902 2 6176,
   opAt 2903 .MLOAD,
   opAt 2904 .JUMPDEST,
   opAt 2905 .GT,
   opAt 2906 .ISZERO,
   pushAt 2907 0 0,
   opAt 2908 .SUB,
   opAt 2909 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2910 .JUMPDEST,
   pushAt 2911 0 0,
   pushAt 2912 2 9440,
   opAt 2913 .MLOAD,
   pushAt 2914 2 9408,
   opAt 2915 .MLOAD,
   pushAt 2916 2 5120,
   opAt 2917 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2918 .JUMPDEST,
   opAt 2919 (.Dup ⟨0, by decide⟩),
   opAt 2920 .MLOAD,
   pushAt 2921 1 0, opAt 2922 .NOT,
   opAt 2923 (.Dup ⟨5, by decide⟩),
   opAt 2924 (.Dup ⟨2, by decide⟩),
   opAt 2925 .MUL,
   opAt 2926 (.Swap ⟨1, by decide⟩),
   opAt 2927 (.Dup ⟨6, by decide⟩),
   opAt 2928 .MULMOD,
   opAt 2929 (.Dup ⟨1, by decide⟩),
   opAt 2930 (.Dup ⟨1, by decide⟩),
   opAt 2931 .LT,
   opAt 2932 .SUB,
   opAt 2933 (.Dup ⟨4, by decide⟩),
   opAt 2934 (.Dup ⟨2, by decide⟩),
   opAt 2935 .ADD,
   opAt 2936 (.Dup ⟨0, by decide⟩),
   opAt 2937 (.Swap ⟨5, by decide⟩),
   opAt 2938 .GT,
   opAt 2939 .SUB,
   opAt 2940 .SUB,
   opAt 2941 (.Dup ⟨3, by decide⟩),
   opAt 2942 (.Dup ⟨3, by decide⟩),
   opAt 2943 .MLOAD,
   opAt 2944 .ADD,
   opAt 2945 (.Dup ⟨0, by decide⟩),
   opAt 2946 (.Swap ⟨4, by decide⟩),
   opAt 2947 .GT,
   opAt 2948 .ADD,
   opAt 2949 (.Swap ⟨2, by decide⟩),
   opAt 2950 (.Dup ⟨2, by decide⟩),
   pushAt 2951 1 31, opAt 2952 .NOT,
   opAt 2953 .ADD,
   opAt 2954 (.Swap ⟨2, by decide⟩),
   opAt 2955 .MSTORE,
   pushAt 2956 1 31, opAt 2957 .NOT,
   opAt 2958 .ADD,
   pushAt 2959 2 8224,
   opAt 2960 (.Dup ⟨2, by decide⟩),
   opAt 2961 .GT,
   pushAt 2962 2 4352,
   opAt 2963 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2964 .POP,
   opAt 2965 .POP,
   pushAt 2966 2 8224,
   opAt 2967 .MLOAD,
   opAt 2968 (.Dup ⟨1, by decide⟩),
   opAt 2969 .ADD,
   opAt 2970 (.Dup ⟨1, by decide⟩),
   opAt 2971 (.Dup ⟨1, by decide⟩),
   opAt 2972 .LT,
   opAt 2973 (.Swap ⟨1, by decide⟩),
   opAt 2974 .POP,
   opAt 2975 (.Dup ⟨2, by decide⟩),
   opAt 2976 (.Dup ⟨1, by decide⟩),
   opAt 2977 .LT,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 (.Dup ⟨3, by decide⟩),
   opAt 2980 (.Swap ⟨0, by decide⟩),
   opAt 2981 .SUB,
   opAt 2982 (.Dup ⟨0, by decide⟩),
   pushAt 2983 2 8224,
   opAt 2984 .MSTORE,
   opAt 2985 .POP,
   opAt 2986 .GT,
   opAt 2987 (.Swap ⟨0, by decide⟩),
   opAt 2988 .POP,
   opAt 2989 .ISZERO,
   pushAt 2990 2 4506,
   opAt 2991 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2992 .JUMPDEST,
   pushAt 2993 0 0,
   pushAt 2994 2 9440,
   opAt 2995 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2996 .JUMPDEST,
   opAt 2997 (.Dup ⟨0, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 (.Dup ⟨1, by decide⟩),
   pushAt 3000 2 8256,
   opAt 3001 (.Swap ⟨0, by decide⟩),
   opAt 3002 .SUB,
   opAt 3003 .MLOAD,
   opAt 3004 (.Dup ⟨1, by decide⟩),
   opAt 3005 .ADD,
   opAt 3006 (.Dup ⟨0, by decide⟩),
   opAt 3007 (.Dup ⟨2, by decide⟩),
   opAt 3008 .GT,
   opAt 3009 (.Swap ⟨1, by decide⟩),
   opAt 3010 .POP,
   opAt 3011 (.Dup ⟨3, by decide⟩),
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨4, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 (.Swap ⟨3, by decide⟩),
   opAt 3017 .POP,
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .MSTORE,
   opAt 3020 (.Swap ⟨0, by decide⟩),
   opAt 3021 (.Swap ⟨1, by decide⟩),
   opAt 3022 .OR,
   opAt 3023 (.Swap ⟨0, by decide⟩),
   pushAt 3024 1 31, opAt 3025 .NOT,
   opAt 3026 .ADD,
   pushAt 3027 2 8255,
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 .GT,
   pushAt 3030 2 4445,
   opAt 3031 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3032 .POP,
   pushAt 3033 2 8224,
   opAt 3034 .MLOAD,
   opAt 3035 (.Dup ⟨1, by decide⟩),
   opAt 3036 .ADD,
   opAt 3037 (.Dup ⟨0, by decide⟩),
   pushAt 3038 2 8224,
   opAt 3039 .MSTORE,
   opAt 3040 .LT,
   opAt 3041 .ISZERO,
   pushAt 3042 2 4439,
   opAt 3043 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3044 .JUMPDEST,
   pushAt 3045 2 8224,
   opAt 3046 .MLOAD,
   opAt 3047 .ISZERO,
   pushAt 3048 2 4575,
   opAt 3049 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3050 0 0,
   pushAt 3051 2 9440,
   opAt 3052 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
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
   opAt 3062 (.Dup ⟨1, by decide⟩),
   opAt 3063 .GT,
   opAt 3064 (.Swap ⟨1, by decide⟩),
   opAt 3065 .SUB,
   opAt 3066 (.Dup ⟨3, by decide⟩),
   opAt 3067 (.Dup ⟨1, by decide⟩),
   opAt 3068 .LT,
   opAt 3069 (.Swap ⟨0, by decide⟩),
   opAt 3070 (.Dup ⟨4, by decide⟩),
   opAt 3071 (.Swap ⟨0, by decide⟩),
   opAt 3072 .SUB,
   opAt 3073 (.Dup ⟨3, by decide⟩),
   opAt 3074 .MSTORE,
   opAt 3075 .OR,
   opAt 3076 (.Swap ⟨1, by decide⟩),
   opAt 3077 .POP,
   pushAt 3078 1 31, opAt 3079 .NOT,
   opAt 3080 .ADD,
   pushAt 3081 2 8255,
   opAt 3082 (.Dup ⟨1, by decide⟩),
   opAt 3083 .GT,
   pushAt 3084 2 4521,
   opAt 3085 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3086 .POP,
   pushAt 3087 2 8224,
   opAt 3088 .MLOAD,
   opAt 3089 .SUB,
   pushAt 3090 2 8224,
   opAt 3091 .MSTORE,
   pushAt 3092 2 4506,
   opAt 3093 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3094 .JUMPDEST,
   pushAt 3095 2 4586,
   pushAt 3096 2 2048,
   pushAt 3097 2 2517,
   opAt 3098 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3099 .JUMPDEST,
   pushAt 3100 1 1,
   opAt 3101 (.Swap ⟨0, by decide⟩),
   opAt 3102 .SUB,
   pushAt 3103 2 4249,
   opAt 3104 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3105 .JUMPDEST,
   opAt 3106 .POP,
   pushAt 3107 2 1756,
   opAt 3108 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4048 = true :=
  Artifact.isValidJumpDest_index 2695 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4092 = true :=
  Artifact.isValidJumpDest_index 2722 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4097 = true :=
  Artifact.isValidJumpDest_index 2725 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4104 = true :=
  Artifact.isValidJumpDest_index 2729 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4135 = true :=
  Artifact.isValidJumpDest_index 2753 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4181 = true :=
  Artifact.isValidJumpDest_index 2790 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4212 = true :=
  Artifact.isValidJumpDest_index 2816 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4249 = true :=
  Artifact.isValidJumpDest_index 2847 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4270 = true :=
  Artifact.isValidJumpDest_index 2860 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4338 = true :=
  Artifact.isValidJumpDest_index 2910 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4352 = true :=
  Artifact.isValidJumpDest_index 2918 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4439 = true :=
  Artifact.isValidJumpDest_index 2992 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4445 = true :=
  Artifact.isValidJumpDest_index 2996 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4506 = true :=
  Artifact.isValidJumpDest_index 3044 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4521 = true :=
  Artifact.isValidJumpDest_index 3053 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4575 = true :=
  Artifact.isValidJumpDest_index 3094 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4586 = true :=
  Artifact.isValidJumpDest_index 3099 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4595 = true :=
  Artifact.isValidJumpDest_index 3105 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
