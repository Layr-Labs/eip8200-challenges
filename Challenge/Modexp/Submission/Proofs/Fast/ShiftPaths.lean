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
  [opAt 2691 .JUMPDEST,
   opAt 2692 (.Dup ⟨0, by decide⟩),
   opAt 2693 (.Dup ⟨3, by decide⟩),
   opAt 2694 .EQ,
   pushAt 2695 0 0,
   opAt 2696 .MLOAD,
   pushAt 2697 1 255,
   opAt 2698 .SHR,
   opAt 2699 .AND,
   opAt 2700 .ISZERO,
   pushAt 2701 2 4581,
   opAt 2702 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2703 (.Dup ⟨0, by decide⟩),
   pushAt 2704 1 96,
   pushAt 2705 2 1024,
   opAt 2706 .CALLDATACOPY,
   opAt 2707 (.Dup ⟨0, by decide⟩),
   pushAt 2708 1 96,
   pushAt 2709 2 8256,
   opAt 2710 .CALLDATACOPY,
   pushAt 2711 0 0,
   pushAt 2712 2 8224,
   opAt 2713 .MSTORE,
   pushAt 2714 2 4586,
   pushAt 2715 2 2048,
   pushAt 2716 2 2638,
   opAt 2717 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2718 .JUMPDEST,
   pushAt 2719 2 1533,
   opAt 2720 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2721 .JUMPDEST,
   pushAt 2722 1 1,
   pushAt 2723 2 9408,
   opAt 2724 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2725 .JUMPDEST,
   opAt 2726 (.Dup ⟨0, by decide⟩),
   opAt 2727 .MLOAD,
   opAt 2728 .NOT,
   opAt 2729 (.Dup ⟨2, by decide⟩),
   opAt 2730 .ADD,
   opAt 2731 (.Dup ⟨2, by decide⟩),
   opAt 2732 (.Dup ⟨1, by decide⟩),
   opAt 2733 .LT,
   opAt 2734 (.Swap ⟨2, by decide⟩),
   opAt 2735 .POP,
   opAt 2736 (.Dup ⟨1, by decide⟩),
   pushAt 2737 2 5120,
   opAt 2738 .ADD,
   opAt 2739 .MSTORE,
   opAt 2740 (.Dup ⟨0, by decide⟩),
   opAt 2741 .ISZERO,
   pushAt 2742 2 4654,
   opAt 2743 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2744 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2745 .ADD,
   pushAt 2746 2 4593,
   opAt 2747 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2748 .JUMPDEST,
   opAt 2749 .POP,
   opAt 2750 .POP,
   pushAt 2751 0 0,
   opAt 2752 .MLOAD,
   opAt 2753 (.Dup ⟨0, by decide⟩),
   pushAt 2754 0 0,
   opAt 2755 .SUB,
   opAt 2756 (.Dup ⟨1, by decide⟩),
   opAt 2757 .AND,
   opAt 2758 (.Dup ⟨0, by decide⟩),
   pushAt 2759 2 6144,
   opAt 2760 .MSTORE,
   opAt 2761 (.Dup ⟨0, by decide⟩),
   opAt 2762 (.Dup ⟨2, by decide⟩),
   opAt 2763 .DIV,
   opAt 2764 (.Dup ⟨0, by decide⟩),
   pushAt 2765 2 6176,
   opAt 2766 .MSTORE,
   opAt 2767 (.Dup ⟨1, by decide⟩),
   pushAt 2768 0 0,
   opAt 2769 .SUB,
   opAt 2770 (.Dup ⟨2, by decide⟩),
   opAt 2771 (.Swap ⟨0, by decide⟩),
   opAt 2772 .DIV,
   pushAt 2773 1 1,
   opAt 2774 .ADD,
   pushAt 2775 2 6208,
   opAt 2776 .MSTORE,
   opAt 2777 (.Dup ⟨0, by decide⟩),
   pushAt 2778 0 0,
   opAt 2779 .SUB,
   opAt 2780 (.Dup ⟨1, by decide⟩),
   opAt 2781 (.Swap ⟨0, by decide⟩),
   opAt 2782 .MOD,
   pushAt 2783 2 6240,
   opAt 2784 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2785 .JUMPDEST,
   pushAt 2786 1 1,
   opAt 2787 (.Dup ⟨0, by decide⟩),
   opAt 2788 (.Dup ⟨2, by decide⟩),
   opAt 2789 .MUL,
   pushAt 2790 1 2,
   opAt 2791 .SUB,
   opAt 2792 .MUL,
   opAt 2793 (.Dup ⟨0, by decide⟩),
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .MUL,
   pushAt 2796 1 2,
   opAt 2797 .SUB,
   opAt 2798 .MUL,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   opAt 2800 (.Dup ⟨2, by decide⟩),
   opAt 2801 .MUL,
   pushAt 2802 1 2,
   opAt 2803 .SUB,
   opAt 2804 .MUL,
   opAt 2805 (.Dup ⟨0, by decide⟩),
   opAt 2806 (.Dup ⟨2, by decide⟩),
   opAt 2807 .MUL,
   pushAt 2808 1 2,
   opAt 2809 .SUB,
   opAt 2810 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2811 .JUMPDEST,
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
   opAt 2829 .MUL,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 (.Dup ⟨2, by decide⟩),
   opAt 2832 .MUL,
   pushAt 2833 1 2,
   opAt 2834 .SUB,
   opAt 2835 .MUL,
   pushAt 2836 2 6272,
   opAt 2837 .MSTORE,
   opAt 2838 .POP,
   opAt 2839 .POP,
   opAt 2840 .POP,
   opAt 2841 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2842 .JUMPDEST,
   opAt 2843 (.Dup ⟨0, by decide⟩),
   opAt 2844 .ISZERO,
   pushAt 2845 2 5260,
   opAt 2846 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2847 (.Dup ⟨1, by decide⟩),
   pushAt 2848 2 2048,
   pushAt 2849 2 8224,
   opAt 2850 .MCOPY,
   pushAt 2851 0 0,
   pushAt 2852 2 9440,
   opAt 2853 .MLOAD,
   opAt 2854 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2855 .JUMPDEST,
   pushAt 2856 2 2048,
   opAt 2857 .MLOAD,
   pushAt 2858 2 6144,
   opAt 2859 .MLOAD,
   opAt 2860 (.Dup ⟨1, by decide⟩),
   opAt 2861 (.Dup ⟨1, by decide⟩),
   opAt 2862 (.Swap ⟨0, by decide⟩),
   opAt 2863 .DIV,
   opAt 2864 (.Swap ⟨1, by decide⟩),
   opAt 2865 .MOD,
   pushAt 2866 2 6208,
   opAt 2867 .MLOAD,
   opAt 2868 .MUL,
   pushAt 2869 2 2080,
   opAt 2870 .MLOAD,
   pushAt 2871 2 6144,
   opAt 2872 .MLOAD,
   opAt 2873 (.Swap ⟨0, by decide⟩),
   opAt 2874 .DIV,
   opAt 2875 .ADD,
   pushAt 2876 2 6176,
   opAt 2877 .MLOAD,
   opAt 2878 (.Dup ⟨0, by decide⟩),
   pushAt 2879 2 6240,
   opAt 2880 .MLOAD,
   opAt 2881 (.Dup ⟨4, by decide⟩),
   opAt 2882 .MULMOD,
   opAt 2883 (.Dup ⟨2, by decide⟩),
   opAt 2884 (.Swap ⟨0, by decide⟩),
   opAt 2885 .ADDMOD,
   opAt 2886 (.Swap ⟨0, by decide⟩),
   opAt 2887 .SUB,
   pushAt 2888 2 6272,
   opAt 2889 .MLOAD,
   opAt 2890 .MUL,
   opAt 2891 (.Dup ⟨0, by decide⟩),
   opAt 2892 .ISZERO,
   opAt 2893 .ISZERO,
   opAt 2894 (.Swap ⟨0, by decide⟩),
   opAt 2895 .SUB,
   opAt 2896 (.Swap ⟨0, by decide⟩),
   opAt 2897 .POP]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2898 .JUMPDEST,
   pushAt 2899 0 0,
   pushAt 2900 2 9440,
   opAt 2901 .MLOAD,
   pushAt 2902 2 9408,
   opAt 2903 .MLOAD,
   pushAt 2904 2 5120,
   opAt 2905 .ADD]

/-- Promoted limb-pass instructions 3077..3119, pc 4862..5009. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2906 .JUMPDEST,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 .MLOAD,
   pushAt 2909 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2910 (.Dup ⟨5, by decide⟩),
   opAt 2911 (.Dup ⟨2, by decide⟩),
   opAt 2912 .MUL,
   opAt 2913 (.Swap ⟨1, by decide⟩),
   opAt 2914 (.Dup ⟨6, by decide⟩),
   opAt 2915 .MULMOD,
   opAt 2916 (.Dup ⟨1, by decide⟩),
   opAt 2917 (.Dup ⟨1, by decide⟩),
   opAt 2918 .LT,
   opAt 2919 .SUB,
   opAt 2920 (.Dup ⟨4, by decide⟩),
   opAt 2921 (.Dup ⟨2, by decide⟩),
   opAt 2922 .ADD,
   opAt 2923 (.Dup ⟨0, by decide⟩),
   opAt 2924 (.Swap ⟨5, by decide⟩),
   opAt 2925 .GT,
   opAt 2926 .SUB,
   opAt 2927 .SUB,
   opAt 2928 (.Dup ⟨3, by decide⟩),
   opAt 2929 (.Dup ⟨3, by decide⟩),
   opAt 2930 .MLOAD,
   opAt 2931 .ADD,
   opAt 2932 (.Dup ⟨0, by decide⟩),
   opAt 2933 (.Swap ⟨4, by decide⟩),
   opAt 2934 .GT,
   opAt 2935 .ADD,
   opAt 2936 (.Swap ⟨2, by decide⟩),
   opAt 2937 (.Dup ⟨2, by decide⟩),
   pushAt 2938 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2939 .ADD,
   opAt 2940 (.Swap ⟨2, by decide⟩),
   opAt 2941 .MSTORE,
   pushAt 2942 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2943 .ADD,
   pushAt 2944 7 8224,
   opAt 2945 (.Dup ⟨2, by decide⟩),
   opAt 2946 .GT,
   pushAt 2947 2 4862,
   opAt 2948 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2949 .POP,
   opAt 2950 .POP,
   pushAt 2951 2 8224,
   opAt 2952 .MLOAD,
   opAt 2953 (.Dup ⟨1, by decide⟩),
   opAt 2954 .ADD,
   opAt 2955 (.Dup ⟨1, by decide⟩),
   opAt 2956 (.Dup ⟨1, by decide⟩),
   opAt 2957 .LT,
   opAt 2958 (.Swap ⟨1, by decide⟩),
   opAt 2959 .POP,
   opAt 2960 (.Dup ⟨2, by decide⟩),
   opAt 2961 (.Dup ⟨1, by decide⟩),
   opAt 2962 .LT,
   opAt 2963 (.Swap ⟨0, by decide⟩),
   opAt 2964 (.Dup ⟨3, by decide⟩),
   opAt 2965 (.Swap ⟨0, by decide⟩),
   opAt 2966 .SUB,
   opAt 2967 (.Dup ⟨0, by decide⟩),
   pushAt 2968 2 8224,
   opAt 2969 .MSTORE,
   opAt 2970 .POP,
   opAt 2971 .GT,
   opAt 2972 (.Swap ⟨0, by decide⟩),
   opAt 2973 .POP,
   opAt 2974 .ISZERO,
   pushAt 2975 2 5141,
   opAt 2976 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2977 .JUMPDEST,
   pushAt 2978 0 0,
   pushAt 2979 2 9440,
   opAt 2980 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2981 .JUMPDEST,
   opAt 2982 (.Dup ⟨0, by decide⟩),
   opAt 2983 .MLOAD,
   opAt 2984 (.Dup ⟨1, by decide⟩),
   pushAt 2985 2 8256,
   opAt 2986 (.Swap ⟨0, by decide⟩),
   opAt 2987 .SUB,
   opAt 2988 .MLOAD,
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 .ADD,
   opAt 2991 (.Dup ⟨0, by decide⟩),
   opAt 2992 (.Dup ⟨2, by decide⟩),
   opAt 2993 .GT,
   opAt 2994 (.Swap ⟨1, by decide⟩),
   opAt 2995 .POP,
   opAt 2996 (.Dup ⟨3, by decide⟩),
   opAt 2997 .ADD,
   opAt 2998 (.Dup ⟨0, by decide⟩),
   opAt 2999 (.Dup ⟨4, by decide⟩),
   opAt 3000 .GT,
   opAt 3001 (.Swap ⟨3, by decide⟩),
   opAt 3002 .POP,
   opAt 3003 (.Dup ⟨2, by decide⟩),
   opAt 3004 .MSTORE,
   opAt 3005 (.Swap ⟨0, by decide⟩),
   opAt 3006 (.Swap ⟨1, by decide⟩),
   opAt 3007 .OR,
   opAt 3008 (.Swap ⟨0, by decide⟩),
   pushAt 3009 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3010 .ADD,
   pushAt 3011 2 8255,
   opAt 3012 (.Dup ⟨1, by decide⟩),
   opAt 3013 .GT,
   pushAt 3014 2 5050,
   opAt 3015 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3016 .POP,
   pushAt 3017 2 8224,
   opAt 3018 .MLOAD,
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 .ADD,
   opAt 3021 (.Dup ⟨0, by decide⟩),
   pushAt 3022 2 8224,
   opAt 3023 .MSTORE,
   opAt 3024 .LT,
   opAt 3025 .ISZERO,
   pushAt 3026 2 5044,
   opAt 3027 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3028 .JUMPDEST,
   pushAt 3029 2 8224,
   opAt 3030 .MLOAD,
   opAt 3031 .ISZERO,
   pushAt 3032 2 5240,
   opAt 3033 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3034 0 0,
   pushAt 3035 2 9440,
   opAt 3036 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3037 .JUMPDEST,
   opAt 3038 (.Dup ⟨0, by decide⟩),
   opAt 3039 .MLOAD,
   opAt 3040 (.Dup ⟨1, by decide⟩),
   pushAt 3041 2 8256,
   opAt 3042 (.Swap ⟨0, by decide⟩),
   opAt 3043 .SUB,
   opAt 3044 .MLOAD,
   opAt 3045 (.Dup ⟨1, by decide⟩),
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 .GT,
   opAt 3048 (.Swap ⟨1, by decide⟩),
   opAt 3049 .SUB,
   opAt 3050 (.Dup ⟨3, by decide⟩),
   opAt 3051 (.Dup ⟨1, by decide⟩),
   opAt 3052 .LT,
   opAt 3053 (.Swap ⟨0, by decide⟩),
   opAt 3054 (.Dup ⟨4, by decide⟩),
   opAt 3055 (.Swap ⟨0, by decide⟩),
   opAt 3056 .SUB,
   opAt 3057 (.Dup ⟨3, by decide⟩),
   opAt 3058 .MSTORE,
   opAt 3059 .OR,
   opAt 3060 (.Swap ⟨1, by decide⟩),
   opAt 3061 .POP,
   pushAt 3062 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3063 .ADD,
   pushAt 3064 2 8255,
   opAt 3065 (.Dup ⟨1, by decide⟩),
   opAt 3066 .GT,
   pushAt 3067 2 5156,
   opAt 3068 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3069 .POP,
   pushAt 3070 2 8224,
   opAt 3071 .MLOAD,
   opAt 3072 .SUB,
   pushAt 3073 2 8224,
   opAt 3074 .MSTORE,
   pushAt 3075 2 5141,
   opAt 3076 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3077 .JUMPDEST,
   pushAt 3078 2 5251,
   pushAt 3079 2 2048,
   pushAt 3080 2 2638,
   opAt 3081 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3082 .JUMPDEST,
   pushAt 3083 1 1,
   opAt 3084 (.Swap ⟨0, by decide⟩),
   opAt 3085 .SUB,
   pushAt 3086 2 4768,
   opAt 3087 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3088 .JUMPDEST,
   opAt 3089 .POP,
   pushAt 3090 2 1756,
   opAt 3091 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4537 = true :=
  Artifact.isValidJumpDest_index 2691 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4581 = true :=
  Artifact.isValidJumpDest_index 2718 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4586 = true :=
  Artifact.isValidJumpDest_index 2721 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4593 = true :=
  Artifact.isValidJumpDest_index 2725 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4654 = true :=
  Artifact.isValidJumpDest_index 2748 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4700 = true :=
  Artifact.isValidJumpDest_index 2785 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4731 = true :=
  Artifact.isValidJumpDest_index 2811 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4768 = true :=
  Artifact.isValidJumpDest_index 2842 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4789 = true :=
  Artifact.isValidJumpDest_index 2855 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4848 = true :=
  Artifact.isValidJumpDest_index 2898 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4862 = true :=
  Artifact.isValidJumpDest_index 2906 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5044 = true :=
  Artifact.isValidJumpDest_index 2977 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5050 = true :=
  Artifact.isValidJumpDest_index 2981 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5141 = true :=
  Artifact.isValidJumpDest_index 3028 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5156 = true :=
  Artifact.isValidJumpDest_index 3037 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5240 = true :=
  Artifact.isValidJumpDest_index 3077 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5251 = true :=
  Artifact.isValidJumpDest_index 3082 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5260 = true :=
  Artifact.isValidJumpDest_index 3088 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
