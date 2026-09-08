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
  [opAt 2694 .JUMPDEST,
   opAt 2695 (.Dup ⟨0, by decide⟩),
   opAt 2696 (.Dup ⟨3, by decide⟩),
   opAt 2697 .EQ,
   pushAt 2698 0 0,
   opAt 2699 .MLOAD,
   pushAt 2700 1 255,
   opAt 2701 .SHR,
   opAt 2702 .AND,
   opAt 2703 .ISZERO,
   pushAt 2704 2 4662,
   opAt 2705 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2706 (.Dup ⟨0, by decide⟩),
   pushAt 2707 1 96,
   pushAt 2708 2 1024,
   opAt 2709 .CALLDATACOPY,
   opAt 2710 (.Dup ⟨0, by decide⟩),
   pushAt 2711 1 96,
   pushAt 2712 2 8256,
   opAt 2713 .CALLDATACOPY,
   pushAt 2714 0 0,
   pushAt 2715 2 8224,
   opAt 2716 .MSTORE,
   pushAt 2717 2 4667,
   pushAt 2718 2 2048,
   pushAt 2719 2 2637,
   opAt 2720 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2721 .JUMPDEST,
   pushAt 2722 2 1533,
   opAt 2723 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2724 .JUMPDEST,
   pushAt 2725 1 1,
   pushAt 2726 2 9408,
   opAt 2727 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2728 .JUMPDEST,
   opAt 2729 (.Dup ⟨0, by decide⟩),
   opAt 2730 .MLOAD,
   opAt 2731 .NOT,
   opAt 2732 (.Dup ⟨2, by decide⟩),
   opAt 2733 .ADD,
   opAt 2734 (.Dup ⟨2, by decide⟩),
   opAt 2735 (.Dup ⟨1, by decide⟩),
   opAt 2736 .LT,
   opAt 2737 (.Swap ⟨2, by decide⟩),
   opAt 2738 .POP,
   opAt 2739 (.Dup ⟨1, by decide⟩),
   pushAt 2740 2 5120,
   opAt 2741 .ADD,
   opAt 2742 .MSTORE,
   opAt 2743 (.Dup ⟨0, by decide⟩),
   opAt 2744 .ISZERO,
   pushAt 2745 2 4735,
   opAt 2746 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2747 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2748 .ADD,
   pushAt 2749 2 4674,
   opAt 2750 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2751 .JUMPDEST,
   opAt 2752 .POP,
   opAt 2753 .POP,
   pushAt 2754 0 0,
   opAt 2755 .MLOAD,
   opAt 2756 (.Dup ⟨0, by decide⟩),
   pushAt 2757 0 0,
   opAt 2758 .SUB,
   opAt 2759 (.Dup ⟨1, by decide⟩),
   opAt 2760 .AND,
   opAt 2761 (.Dup ⟨0, by decide⟩),
   pushAt 2762 2 6144,
   opAt 2763 .MSTORE,
   opAt 2764 (.Dup ⟨0, by decide⟩),
   opAt 2765 (.Dup ⟨2, by decide⟩),
   opAt 2766 .DIV,
   opAt 2767 (.Dup ⟨0, by decide⟩),
   pushAt 2768 2 6176,
   opAt 2769 .MSTORE,
   opAt 2770 (.Dup ⟨1, by decide⟩),
   pushAt 2771 0 0,
   opAt 2772 .SUB,
   opAt 2773 (.Dup ⟨2, by decide⟩),
   opAt 2774 (.Swap ⟨0, by decide⟩),
   opAt 2775 .DIV,
   pushAt 2776 1 1,
   opAt 2777 .ADD,
   pushAt 2778 2 6208,
   opAt 2779 .MSTORE,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   pushAt 2781 0 0,
   opAt 2782 .SUB,
   opAt 2783 (.Dup ⟨1, by decide⟩),
   opAt 2784 (.Swap ⟨0, by decide⟩),
   opAt 2785 .MOD,
   pushAt 2786 2 6240,
   opAt 2787 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2788 .JUMPDEST,
   pushAt 2789 1 1,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   opAt 2791 (.Dup ⟨2, by decide⟩),
   opAt 2792 .MUL,
   pushAt 2793 1 2,
   opAt 2794 .SUB,
   opAt 2795 .MUL,
   opAt 2796 (.Dup ⟨0, by decide⟩),
   opAt 2797 (.Dup ⟨2, by decide⟩),
   opAt 2798 .MUL,
   pushAt 2799 1 2,
   opAt 2800 .SUB,
   opAt 2801 .MUL,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   opAt 2803 (.Dup ⟨2, by decide⟩),
   opAt 2804 .MUL,
   pushAt 2805 1 2,
   opAt 2806 .SUB,
   opAt 2807 .MUL,
   opAt 2808 (.Dup ⟨0, by decide⟩),
   opAt 2809 (.Dup ⟨2, by decide⟩),
   opAt 2810 .MUL,
   pushAt 2811 1 2,
   opAt 2812 .SUB,
   opAt 2813 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2814 .JUMPDEST,
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
   opAt 2826 .MUL,
   opAt 2827 (.Dup ⟨0, by decide⟩),
   opAt 2828 (.Dup ⟨2, by decide⟩),
   opAt 2829 .MUL,
   pushAt 2830 1 2,
   opAt 2831 .SUB,
   opAt 2832 .MUL,
   opAt 2833 (.Dup ⟨0, by decide⟩),
   opAt 2834 (.Dup ⟨2, by decide⟩),
   opAt 2835 .MUL,
   pushAt 2836 1 2,
   opAt 2837 .SUB,
   opAt 2838 .MUL,
   pushAt 2839 2 6272,
   opAt 2840 .MSTORE,
   opAt 2841 .POP,
   opAt 2842 .POP,
   opAt 2843 .POP,
   opAt 2844 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2845 .JUMPDEST,
   opAt 2846 (.Dup ⟨0, by decide⟩),
   opAt 2847 .ISZERO,
   pushAt 2848 2 5345,
   opAt 2849 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2850 (.Dup ⟨1, by decide⟩),
   pushAt 2851 2 2048,
   pushAt 2852 2 8224,
   opAt 2853 .MCOPY,
   pushAt 2854 0 0,
   pushAt 2855 2 9440,
   opAt 2856 .MLOAD,
   opAt 2857 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2858 .JUMPDEST,
   pushAt 2859 2 2048,
   opAt 2860 .MLOAD,
   pushAt 2861 2 6144,
   opAt 2862 .MLOAD,
   opAt 2863 (.Dup ⟨1, by decide⟩),
   opAt 2864 (.Dup ⟨1, by decide⟩),
   opAt 2865 (.Swap ⟨0, by decide⟩),
   opAt 2866 .DIV,
   opAt 2867 (.Swap ⟨1, by decide⟩),
   opAt 2868 .MOD,
   pushAt 2869 2 6208,
   opAt 2870 .MLOAD,
   opAt 2871 .MUL,
   pushAt 2872 2 2080,
   opAt 2873 .MLOAD,
   pushAt 2874 2 6144,
   opAt 2875 .MLOAD,
   opAt 2876 (.Swap ⟨0, by decide⟩),
   opAt 2877 .DIV,
   opAt 2878 .ADD,
   pushAt 2879 2 6176,
   opAt 2880 .MLOAD,
   opAt 2881 (.Dup ⟨0, by decide⟩),
   pushAt 2882 2 6240,
   opAt 2883 .MLOAD,
   opAt 2884 (.Dup ⟨4, by decide⟩),
   opAt 2885 .MULMOD,
   opAt 2886 (.Dup ⟨2, by decide⟩),
   opAt 2887 (.Swap ⟨0, by decide⟩),
   opAt 2888 .ADDMOD,
   opAt 2889 (.Swap ⟨0, by decide⟩),
   opAt 2890 .SUB,
   pushAt 2891 2 6272,
   opAt 2892 .MLOAD,
   opAt 2893 .MUL,
   opAt 2894 (.Dup ⟨0, by decide⟩),
   opAt 2895 .ISZERO,
   opAt 2896 .ISZERO,
   opAt 2897 (.Swap ⟨0, by decide⟩),
   opAt 2898 .SUB,
   opAt 2899 (.Swap ⟨0, by decide⟩),
   pushAt 2900 2 6176,
   opAt 2901 .MLOAD,
   opAt 2902 (.Swap ⟨0, by decide⟩),
   opAt 2903 .LT,
   opAt 2904 .ISZERO,
   pushAt 2905 0 0,
   opAt 2906 .SUB,
   opAt 2907 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2908 .JUMPDEST,
   pushAt 2909 0 0,
   pushAt 2910 2 9440,
   opAt 2911 .MLOAD,
   pushAt 2912 2 9408,
   opAt 2913 .MLOAD,
   pushAt 2914 2 5120,
   opAt 2915 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2916 .JUMPDEST,
   opAt 2917 (.Dup ⟨0, by decide⟩),
   opAt 2918 .MLOAD,
   pushAt 2919 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2920 (.Dup ⟨5, by decide⟩),
   opAt 2921 (.Dup ⟨2, by decide⟩),
   opAt 2922 .MUL,
   opAt 2923 (.Swap ⟨1, by decide⟩),
   opAt 2924 (.Dup ⟨6, by decide⟩),
   opAt 2925 .MULMOD,
   opAt 2926 (.Dup ⟨1, by decide⟩),
   opAt 2927 (.Dup ⟨1, by decide⟩),
   opAt 2928 .LT,
   opAt 2929 .SUB,
   opAt 2930 (.Dup ⟨4, by decide⟩),
   opAt 2931 (.Dup ⟨2, by decide⟩),
   opAt 2932 .ADD,
   opAt 2933 (.Dup ⟨0, by decide⟩),
   opAt 2934 (.Swap ⟨5, by decide⟩),
   opAt 2935 .GT,
   opAt 2936 .SUB,
   opAt 2937 .SUB,
   opAt 2938 (.Dup ⟨3, by decide⟩),
   opAt 2939 (.Dup ⟨3, by decide⟩),
   opAt 2940 .MLOAD,
   opAt 2941 .ADD,
   opAt 2942 (.Dup ⟨0, by decide⟩),
   opAt 2943 (.Swap ⟨4, by decide⟩),
   opAt 2944 .GT,
   opAt 2945 .ADD,
   opAt 2946 (.Swap ⟨2, by decide⟩),
   opAt 2947 (.Dup ⟨2, by decide⟩),
   pushAt 2948 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2949 .ADD,
   opAt 2950 (.Swap ⟨2, by decide⟩),
   opAt 2951 .MSTORE,
   pushAt 2952 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2953 .ADD,
   pushAt 2954 2 8224,
   opAt 2955 (.Dup ⟨2, by decide⟩),
   opAt 2956 .GT,
   pushAt 2957 2 4952,
   opAt 2958 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2959 .POP,
   opAt 2960 .POP,
   pushAt 2961 2 8224,
   opAt 2962 .MLOAD,
   opAt 2963 (.Dup ⟨1, by decide⟩),
   opAt 2964 .ADD,
   opAt 2965 (.Dup ⟨1, by decide⟩),
   opAt 2966 (.Dup ⟨1, by decide⟩),
   opAt 2967 .LT,
   opAt 2968 (.Swap ⟨1, by decide⟩),
   opAt 2969 .POP,
   opAt 2970 (.Dup ⟨2, by decide⟩),
   opAt 2971 (.Dup ⟨1, by decide⟩),
   opAt 2972 .LT,
   opAt 2973 (.Swap ⟨0, by decide⟩),
   opAt 2974 (.Dup ⟨3, by decide⟩),
   opAt 2975 (.Swap ⟨0, by decide⟩),
   opAt 2976 .SUB,
   opAt 2977 (.Dup ⟨0, by decide⟩),
   pushAt 2978 2 8224,
   opAt 2979 .MSTORE,
   opAt 2980 .POP,
   opAt 2981 .GT,
   opAt 2982 (.Swap ⟨0, by decide⟩),
   opAt 2983 .POP,
   opAt 2984 .ISZERO,
   pushAt 2985 2 5226,
   opAt 2986 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2987 .JUMPDEST,
   pushAt 2988 0 0,
   pushAt 2989 2 9440,
   opAt 2990 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2991 .JUMPDEST,
   opAt 2992 (.Dup ⟨0, by decide⟩),
   opAt 2993 .MLOAD,
   opAt 2994 (.Dup ⟨1, by decide⟩),
   pushAt 2995 2 8256,
   opAt 2996 (.Swap ⟨0, by decide⟩),
   opAt 2997 .SUB,
   opAt 2998 .MLOAD,
   opAt 2999 (.Dup ⟨1, by decide⟩),
   opAt 3000 .ADD,
   opAt 3001 (.Dup ⟨0, by decide⟩),
   opAt 3002 (.Dup ⟨2, by decide⟩),
   opAt 3003 .GT,
   opAt 3004 (.Swap ⟨1, by decide⟩),
   opAt 3005 .POP,
   opAt 3006 (.Dup ⟨3, by decide⟩),
   opAt 3007 .ADD,
   opAt 3008 (.Dup ⟨0, by decide⟩),
   opAt 3009 (.Dup ⟨4, by decide⟩),
   opAt 3010 .GT,
   opAt 3011 (.Swap ⟨3, by decide⟩),
   opAt 3012 .POP,
   opAt 3013 (.Dup ⟨2, by decide⟩),
   opAt 3014 .MSTORE,
   opAt 3015 (.Swap ⟨0, by decide⟩),
   opAt 3016 (.Swap ⟨1, by decide⟩),
   opAt 3017 .OR,
   opAt 3018 (.Swap ⟨0, by decide⟩),
   pushAt 3019 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3020 .ADD,
   pushAt 3021 2 8255,
   opAt 3022 (.Dup ⟨1, by decide⟩),
   opAt 3023 .GT,
   pushAt 3024 2 5135,
   opAt 3025 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3026 .POP,
   pushAt 3027 2 8224,
   opAt 3028 .MLOAD,
   opAt 3029 (.Dup ⟨1, by decide⟩),
   opAt 3030 .ADD,
   opAt 3031 (.Dup ⟨0, by decide⟩),
   pushAt 3032 2 8224,
   opAt 3033 .MSTORE,
   opAt 3034 .LT,
   opAt 3035 .ISZERO,
   pushAt 3036 2 5129,
   opAt 3037 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3038 .JUMPDEST,
   pushAt 3039 2 8224,
   opAt 3040 .MLOAD,
   opAt 3041 .ISZERO,
   pushAt 3042 2 5325,
   opAt 3043 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3044 0 0,
   pushAt 3045 2 9440,
   opAt 3046 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3047 .JUMPDEST,
   opAt 3048 (.Dup ⟨0, by decide⟩),
   opAt 3049 .MLOAD,
   opAt 3050 (.Dup ⟨1, by decide⟩),
   pushAt 3051 2 8256,
   opAt 3052 (.Swap ⟨0, by decide⟩),
   opAt 3053 .SUB,
   opAt 3054 .MLOAD,
   opAt 3055 (.Dup ⟨1, by decide⟩),
   opAt 3056 (.Dup ⟨1, by decide⟩),
   opAt 3057 .GT,
   opAt 3058 (.Swap ⟨1, by decide⟩),
   opAt 3059 .SUB,
   opAt 3060 (.Dup ⟨3, by decide⟩),
   opAt 3061 (.Dup ⟨1, by decide⟩),
   opAt 3062 .LT,
   opAt 3063 (.Swap ⟨0, by decide⟩),
   opAt 3064 (.Dup ⟨4, by decide⟩),
   opAt 3065 (.Swap ⟨0, by decide⟩),
   opAt 3066 .SUB,
   opAt 3067 (.Dup ⟨3, by decide⟩),
   opAt 3068 .MSTORE,
   opAt 3069 .OR,
   opAt 3070 (.Swap ⟨1, by decide⟩),
   opAt 3071 .POP,
   pushAt 3072 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3073 .ADD,
   pushAt 3074 2 8255,
   opAt 3075 (.Dup ⟨1, by decide⟩),
   opAt 3076 .GT,
   pushAt 3077 2 5241,
   opAt 3078 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3079 .POP,
   pushAt 3080 2 8224,
   opAt 3081 .MLOAD,
   opAt 3082 .SUB,
   pushAt 3083 2 8224,
   opAt 3084 .MSTORE,
   pushAt 3085 2 5226,
   opAt 3086 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3087 .JUMPDEST,
   pushAt 3088 2 5336,
   pushAt 3089 2 2048,
   pushAt 3090 2 2637,
   opAt 3091 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3092 .JUMPDEST,
   pushAt 3093 1 1,
   opAt 3094 (.Swap ⟨0, by decide⟩),
   opAt 3095 .SUB,
   pushAt 3096 2 4849,
   opAt 3097 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3098 .JUMPDEST,
   opAt 3099 .POP,
   pushAt 3100 2 1756,
   opAt 3101 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4618 = true :=
  Artifact.isValidJumpDest_index 2694 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4662 = true :=
  Artifact.isValidJumpDest_index 2721 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4667 = true :=
  Artifact.isValidJumpDest_index 2724 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4674 = true :=
  Artifact.isValidJumpDest_index 2728 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 2751 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4781 = true :=
  Artifact.isValidJumpDest_index 2788 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4812 = true :=
  Artifact.isValidJumpDest_index 2814 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4849 = true :=
  Artifact.isValidJumpDest_index 2845 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4870 = true :=
  Artifact.isValidJumpDest_index 2858 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4938 = true :=
  Artifact.isValidJumpDest_index 2908 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4952 = true :=
  Artifact.isValidJumpDest_index 2916 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5129 = true :=
  Artifact.isValidJumpDest_index 2987 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5135 = true :=
  Artifact.isValidJumpDest_index 2991 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5226 = true :=
  Artifact.isValidJumpDest_index 3038 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5241 = true :=
  Artifact.isValidJumpDest_index 3047 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5325 = true :=
  Artifact.isValidJumpDest_index 3087 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5336 = true :=
  Artifact.isValidJumpDest_index 3092 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5345 = true :=
  Artifact.isValidJumpDest_index 3098 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
