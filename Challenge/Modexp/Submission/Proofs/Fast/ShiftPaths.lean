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
  [opAt 2707 .JUMPDEST,
   opAt 2708 (.Dup ⟨0, by decide⟩),
   opAt 2709 (.Dup ⟨3, by decide⟩),
   opAt 2710 .EQ,
   pushAt 2711 0 0,
   opAt 2712 .MLOAD,
   pushAt 2713 1 255,
   opAt 2714 .SHR,
   opAt 2715 .AND,
   opAt 2716 .ISZERO,
   pushAt 2717 2 4515,
   opAt 2718 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2719 (.Dup ⟨0, by decide⟩),
   pushAt 2720 1 96,
   pushAt 2721 2 1024,
   opAt 2722 .CALLDATACOPY,
   opAt 2723 (.Dup ⟨0, by decide⟩),
   pushAt 2724 1 96,
   pushAt 2725 2 8256,
   opAt 2726 .CALLDATACOPY,
   pushAt 2727 0 0,
   pushAt 2728 2 8224,
   opAt 2729 .MSTORE,
   pushAt 2730 2 4520,
   pushAt 2731 2 2048,
   pushAt 2732 2 2497,
   opAt 2733 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2734 .JUMPDEST,
   pushAt 2735 2 1520,
   opAt 2736 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2737 .JUMPDEST,
   pushAt 2738 1 1,
   pushAt 2739 2 9408,
   opAt 2740 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2741 .JUMPDEST,
   opAt 2742 (.Dup ⟨0, by decide⟩),
   opAt 2743 .MLOAD,
   opAt 2744 .NOT,
   opAt 2745 (.Dup ⟨2, by decide⟩),
   opAt 2746 .ADD,
   opAt 2747 (.Dup ⟨2, by decide⟩),
   opAt 2748 (.Dup ⟨1, by decide⟩),
   opAt 2749 .LT,
   opAt 2750 (.Swap ⟨2, by decide⟩),
   opAt 2751 .POP,
   opAt 2752 (.Dup ⟨1, by decide⟩),
   pushAt 2753 2 5120,
   opAt 2754 .ADD,
   opAt 2755 .MSTORE,
   opAt 2756 (.Dup ⟨0, by decide⟩),
   opAt 2757 .ISZERO,
   pushAt 2758 2 4588,
   opAt 2759 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2760 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2761 .ADD,
   pushAt 2762 2 4527,
   opAt 2763 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2764 .JUMPDEST,
   opAt 2765 .POP,
   opAt 2766 .POP,
   pushAt 2767 0 0,
   opAt 2768 .MLOAD,
   opAt 2769 (.Dup ⟨0, by decide⟩),
   pushAt 2770 0 0,
   opAt 2771 .SUB,
   opAt 2772 (.Dup ⟨1, by decide⟩),
   opAt 2773 .AND,
   opAt 2774 (.Dup ⟨0, by decide⟩),
   pushAt 2775 2 6144,
   opAt 2776 .MSTORE,
   opAt 2777 (.Dup ⟨0, by decide⟩),
   opAt 2778 (.Dup ⟨2, by decide⟩),
   opAt 2779 .DIV,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   pushAt 2781 2 6176,
   opAt 2782 .MSTORE,
   opAt 2783 (.Dup ⟨1, by decide⟩),
   pushAt 2784 0 0,
   opAt 2785 .SUB,
   opAt 2786 (.Dup ⟨2, by decide⟩),
   opAt 2787 (.Swap ⟨0, by decide⟩),
   opAt 2788 .DIV,
   pushAt 2789 1 1,
   opAt 2790 .ADD,
   pushAt 2791 2 6208,
   opAt 2792 .MSTORE,
   opAt 2793 (.Dup ⟨0, by decide⟩),
   pushAt 2794 0 0,
   opAt 2795 .SUB,
   opAt 2796 (.Dup ⟨1, by decide⟩),
   opAt 2797 (.Swap ⟨0, by decide⟩),
   opAt 2798 .MOD,
   pushAt 2799 2 6240,
   opAt 2800 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2801 .JUMPDEST,
   pushAt 2802 1 1,
   opAt 2803 (.Dup ⟨0, by decide⟩),
   opAt 2804 (.Dup ⟨2, by decide⟩),
   opAt 2805 .MUL,
   pushAt 2806 1 2,
   opAt 2807 .SUB,
   opAt 2808 .MUL,
   opAt 2809 (.Dup ⟨0, by decide⟩),
   opAt 2810 (.Dup ⟨2, by decide⟩),
   opAt 2811 .MUL,
   pushAt 2812 1 2,
   opAt 2813 .SUB,
   opAt 2814 .MUL,
   opAt 2815 (.Dup ⟨0, by decide⟩),
   opAt 2816 (.Dup ⟨2, by decide⟩),
   opAt 2817 .MUL,
   pushAt 2818 1 2,
   opAt 2819 .SUB,
   opAt 2820 .MUL,
   opAt 2821 (.Dup ⟨0, by decide⟩),
   opAt 2822 (.Dup ⟨2, by decide⟩),
   opAt 2823 .MUL,
   pushAt 2824 1 2,
   opAt 2825 .SUB,
   opAt 2826 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2827 .JUMPDEST,
   opAt 2828 (.Dup ⟨0, by decide⟩),
   opAt 2829 (.Dup ⟨2, by decide⟩),
   opAt 2830 .MUL,
   pushAt 2831 1 2,
   opAt 2832 .SUB,
   opAt 2833 .MUL,
   opAt 2834 (.Dup ⟨0, by decide⟩),
   opAt 2835 (.Dup ⟨2, by decide⟩),
   opAt 2836 .MUL,
   pushAt 2837 1 2,
   opAt 2838 .SUB,
   opAt 2839 .MUL,
   opAt 2840 (.Dup ⟨0, by decide⟩),
   opAt 2841 (.Dup ⟨2, by decide⟩),
   opAt 2842 .MUL,
   pushAt 2843 1 2,
   opAt 2844 .SUB,
   opAt 2845 .MUL,
   opAt 2846 (.Dup ⟨0, by decide⟩),
   opAt 2847 (.Dup ⟨2, by decide⟩),
   opAt 2848 .MUL,
   pushAt 2849 1 2,
   opAt 2850 .SUB,
   opAt 2851 .MUL,
   pushAt 2852 2 6272,
   opAt 2853 .MSTORE,
   opAt 2854 .POP,
   opAt 2855 .POP,
   opAt 2856 .POP,
   opAt 2857 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2858 .JUMPDEST,
   opAt 2859 (.Dup ⟨0, by decide⟩),
   opAt 2860 .ISZERO,
   pushAt 2861 2 5197,
   opAt 2862 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2863 (.Dup ⟨1, by decide⟩),
   pushAt 2864 2 2048,
   pushAt 2865 2 8224,
   opAt 2866 .MCOPY,
   pushAt 2867 0 0,
   pushAt 2868 2 9440,
   opAt 2869 .MLOAD,
   opAt 2870 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2871 .JUMPDEST,
   pushAt 2872 2 2048,
   opAt 2873 .MLOAD,
   pushAt 2874 2 6144,
   opAt 2875 .MLOAD,
   opAt 2876 (.Dup ⟨1, by decide⟩),
   opAt 2877 (.Dup ⟨1, by decide⟩),
   opAt 2878 (.Swap ⟨0, by decide⟩),
   opAt 2879 .DIV,
   opAt 2880 (.Swap ⟨1, by decide⟩),
   opAt 2881 .MOD,
   pushAt 2882 2 6208,
   opAt 2883 .MLOAD,
   opAt 2884 .MUL,
   pushAt 2885 2 2080,
   opAt 2886 .MLOAD,
   pushAt 2887 2 6144,
   opAt 2888 .MLOAD,
   opAt 2889 (.Swap ⟨0, by decide⟩),
   opAt 2890 .DIV,
   opAt 2891 .ADD,
   pushAt 2892 2 6176,
   opAt 2893 .MLOAD,
   opAt 2894 (.Dup ⟨0, by decide⟩),
   pushAt 2895 2 6240,
   opAt 2896 .MLOAD,
   opAt 2897 (.Dup ⟨4, by decide⟩),
   opAt 2898 .MULMOD,
   opAt 2899 (.Dup ⟨2, by decide⟩),
   opAt 2900 (.Swap ⟨0, by decide⟩),
   opAt 2901 .ADDMOD,
   opAt 2902 (.Swap ⟨0, by decide⟩),
   opAt 2903 .SUB,
   pushAt 2904 2 6272,
   opAt 2905 .MLOAD,
   opAt 2906 .MUL,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 .ISZERO,
   opAt 2909 .ISZERO,
   opAt 2910 (.Swap ⟨0, by decide⟩),
   opAt 2911 .SUB,
   opAt 2912 (.Swap ⟨0, by decide⟩),
   pushAt 2913 2 6176,
   opAt 2914 .MLOAD,
      opAt 2915 .GT,
   opAt 2916 .ISZERO,
   pushAt 2917 0 0,
   opAt 2918 .SUB,
   opAt 2919 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2920 .JUMPDEST,
   pushAt 2921 0 0,
   pushAt 2922 2 9440,
   opAt 2923 .MLOAD,
   pushAt 2924 2 9408,
   opAt 2925 .MLOAD,
   pushAt 2926 2 5120,
   opAt 2927 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2928 .JUMPDEST,
   opAt 2929 (.Dup ⟨0, by decide⟩),
   opAt 2930 .MLOAD,
   pushAt 2931 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2932 (.Dup ⟨5, by decide⟩),
   opAt 2933 (.Dup ⟨2, by decide⟩),
   opAt 2934 .MUL,
   opAt 2935 (.Swap ⟨1, by decide⟩),
   opAt 2936 (.Dup ⟨6, by decide⟩),
   opAt 2937 .MULMOD,
   opAt 2938 (.Dup ⟨1, by decide⟩),
   opAt 2939 (.Dup ⟨1, by decide⟩),
   opAt 2940 .LT,
   opAt 2941 .SUB,
   opAt 2942 (.Dup ⟨4, by decide⟩),
   opAt 2943 (.Dup ⟨2, by decide⟩),
   opAt 2944 .ADD,
   opAt 2945 (.Dup ⟨0, by decide⟩),
   opAt 2946 (.Swap ⟨5, by decide⟩),
   opAt 2947 .GT,
   opAt 2948 .SUB,
   opAt 2949 .SUB,
   opAt 2950 (.Dup ⟨3, by decide⟩),
   opAt 2951 (.Dup ⟨3, by decide⟩),
   opAt 2952 .MLOAD,
   opAt 2953 .ADD,
   opAt 2954 (.Dup ⟨0, by decide⟩),
   opAt 2955 (.Swap ⟨4, by decide⟩),
   opAt 2956 .GT,
   opAt 2957 .ADD,
   opAt 2958 (.Swap ⟨2, by decide⟩),
   opAt 2959 (.Dup ⟨2, by decide⟩),
   pushAt 2960 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2961 .ADD,
   opAt 2962 (.Swap ⟨2, by decide⟩),
   opAt 2963 .MSTORE,
   pushAt 2964 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2965 .ADD,
   pushAt 2966 2 8224,
   opAt 2967 (.Dup ⟨2, by decide⟩),
   opAt 2968 .GT,
   pushAt 2969 2 4804,
   opAt 2970 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2971 .POP,
   opAt 2972 .POP,
   pushAt 2973 2 8224,
   opAt 2974 .MLOAD,
   opAt 2975 (.Dup ⟨1, by decide⟩),
   opAt 2976 .ADD,
   opAt 2977 (.Dup ⟨1, by decide⟩),
   opAt 2978 (.Dup ⟨1, by decide⟩),
   opAt 2979 .LT,
   opAt 2980 (.Swap ⟨1, by decide⟩),
   opAt 2981 .POP,
   opAt 2982 (.Dup ⟨2, by decide⟩),
   opAt 2983 (.Dup ⟨1, by decide⟩),
   opAt 2984 .LT,
   opAt 2985 (.Swap ⟨0, by decide⟩),
   opAt 2986 (.Dup ⟨3, by decide⟩),
   opAt 2987 (.Swap ⟨0, by decide⟩),
   opAt 2988 .SUB,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   pushAt 2990 2 8224,
   opAt 2991 .MSTORE,
   opAt 2992 .POP,
   opAt 2993 .GT,
   opAt 2994 (.Swap ⟨0, by decide⟩),
   opAt 2995 .POP,
   opAt 2996 .ISZERO,
   pushAt 2997 2 5078,
   opAt 2998 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2999 .JUMPDEST,
   pushAt 3000 0 0,
   pushAt 3001 2 9440,
   opAt 3002 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3003 .JUMPDEST,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 .MLOAD,
   opAt 3006 (.Dup ⟨1, by decide⟩),
   pushAt 3007 2 8256,
   opAt 3008 (.Swap ⟨0, by decide⟩),
   opAt 3009 .SUB,
   opAt 3010 .MLOAD,
   opAt 3011 (.Dup ⟨1, by decide⟩),
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨2, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 (.Swap ⟨1, by decide⟩),
   opAt 3017 .POP,
   opAt 3018 (.Dup ⟨3, by decide⟩),
   opAt 3019 .ADD,
   opAt 3020 (.Dup ⟨0, by decide⟩),
   opAt 3021 (.Dup ⟨4, by decide⟩),
   opAt 3022 .GT,
   opAt 3023 (.Swap ⟨3, by decide⟩),
   opAt 3024 .POP,
   opAt 3025 (.Dup ⟨2, by decide⟩),
   opAt 3026 .MSTORE,
   opAt 3027 (.Swap ⟨0, by decide⟩),
   opAt 3028 (.Swap ⟨1, by decide⟩),
   opAt 3029 .OR,
   opAt 3030 (.Swap ⟨0, by decide⟩),
   pushAt 3031 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3032 .ADD,
   pushAt 3033 2 8255,
   opAt 3034 (.Dup ⟨1, by decide⟩),
   opAt 3035 .GT,
   pushAt 3036 2 4987,
   opAt 3037 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3038 .POP,
   pushAt 3039 2 8224,
   opAt 3040 .MLOAD,
   opAt 3041 (.Dup ⟨1, by decide⟩),
   opAt 3042 .ADD,
   opAt 3043 (.Dup ⟨0, by decide⟩),
   pushAt 3044 2 8224,
   opAt 3045 .MSTORE,
   opAt 3046 .LT,
   opAt 3047 .ISZERO,
   pushAt 3048 2 4981,
   opAt 3049 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3050 .JUMPDEST,
   pushAt 3051 2 8224,
   opAt 3052 .MLOAD,
   opAt 3053 .ISZERO,
   pushAt 3054 2 5177,
   opAt 3055 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3056 0 0,
   pushAt 3057 2 9440,
   opAt 3058 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
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
   opAt 3068 (.Dup ⟨1, by decide⟩),
   opAt 3069 .GT,
   opAt 3070 (.Swap ⟨1, by decide⟩),
   opAt 3071 .SUB,
   opAt 3072 (.Dup ⟨3, by decide⟩),
   opAt 3073 (.Dup ⟨1, by decide⟩),
   opAt 3074 .LT,
   opAt 3075 (.Swap ⟨0, by decide⟩),
   opAt 3076 (.Dup ⟨4, by decide⟩),
   opAt 3077 (.Swap ⟨0, by decide⟩),
   opAt 3078 .SUB,
   opAt 3079 (.Dup ⟨3, by decide⟩),
   opAt 3080 .MSTORE,
   opAt 3081 .OR,
   opAt 3082 (.Swap ⟨1, by decide⟩),
   opAt 3083 .POP,
   pushAt 3084 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3085 .ADD,
   pushAt 3086 2 8255,
   opAt 3087 (.Dup ⟨1, by decide⟩),
   opAt 3088 .GT,
   pushAt 3089 2 5093,
   opAt 3090 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3091 .POP,
   pushAt 3092 2 8224,
   opAt 3093 .MLOAD,
   opAt 3094 .SUB,
   pushAt 3095 2 8224,
   opAt 3096 .MSTORE,
   pushAt 3097 2 5078,
   opAt 3098 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3099 .JUMPDEST,
   pushAt 3100 2 5188,
   pushAt 3101 2 2048,
   pushAt 3102 2 2497,
   opAt 3103 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3104 .JUMPDEST,
   pushAt 3105 1 1,
   opAt 3106 (.Swap ⟨0, by decide⟩),
   opAt 3107 .SUB,
   pushAt 3108 2 4702,
   opAt 3109 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3110 .JUMPDEST,
   opAt 3111 .POP,
   pushAt 3112 2 1730,
   opAt 3113 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4471 = true :=
  Artifact.isValidJumpDest_index 2707 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4515 = true :=
  Artifact.isValidJumpDest_index 2734 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4520 = true :=
  Artifact.isValidJumpDest_index 2737 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4527 = true :=
  Artifact.isValidJumpDest_index 2741 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4588 = true :=
  Artifact.isValidJumpDest_index 2764 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4634 = true :=
  Artifact.isValidJumpDest_index 2801 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4665 = true :=
  Artifact.isValidJumpDest_index 2827 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4702 = true :=
  Artifact.isValidJumpDest_index 2858 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4723 = true :=
  Artifact.isValidJumpDest_index 2871 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4790 = true :=
  Artifact.isValidJumpDest_index 2920 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4804 = true :=
  Artifact.isValidJumpDest_index 2928 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4981 = true :=
  Artifact.isValidJumpDest_index 2999 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4987 = true :=
  Artifact.isValidJumpDest_index 3003 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5078 = true :=
  Artifact.isValidJumpDest_index 3050 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5093 = true :=
  Artifact.isValidJumpDest_index 3059 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5177 = true :=
  Artifact.isValidJumpDest_index 3099 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5188 = true :=
  Artifact.isValidJumpDest_index 3104 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5197 = true :=
  Artifact.isValidJumpDest_index 3110 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
