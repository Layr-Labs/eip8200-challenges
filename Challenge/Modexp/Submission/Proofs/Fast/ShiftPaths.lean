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
  [opAt 2684 .JUMPDEST,
   opAt 2685 (.Dup ⟨0, by decide⟩),
   opAt 2686 (.Dup ⟨3, by decide⟩),
   opAt 2687 .EQ,
   pushAt 2688 0 0,
   opAt 2689 .MLOAD,
   pushAt 2690 1 255,
   opAt 2691 .SHR,
   opAt 2692 .AND,
   opAt 2693 .ISZERO,
   pushAt 2694 2 1533,
   opAt 2695 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2696 (.Dup ⟨0, by decide⟩),
   pushAt 2697 1 96,
   pushAt 2698 2 1024,
   opAt 2699 .CALLDATACOPY,
   opAt 2700 (.Dup ⟨0, by decide⟩),
   pushAt 2701 1 96,
   pushAt 2702 2 8256,
   opAt 2703 .CALLDATACOPY,
   pushAt 2704 0 0,
   pushAt 2705 2 8224,
   opAt 2706 .MSTORE,
   pushAt 2707 2 4667,
   pushAt 2708 2 2048,
   pushAt 2709 2 2637,
   opAt 2710 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2711 .JUMPDEST,
   pushAt 2712 2 1533,
   opAt 2713 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2714 .JUMPDEST,
   pushAt 2715 1 1,
   pushAt 2716 2 9408,
   opAt 2717 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2718 .JUMPDEST,
   opAt 2719 (.Dup ⟨0, by decide⟩),
   opAt 2720 .MLOAD,
   opAt 2721 .NOT,
   opAt 2722 (.Dup ⟨2, by decide⟩),
   opAt 2723 .ADD,
   opAt 2724 (.Dup ⟨2, by decide⟩),
   opAt 2725 (.Dup ⟨1, by decide⟩),
   opAt 2726 .LT,
   opAt 2727 (.Swap ⟨2, by decide⟩),
   opAt 2728 .POP,
   opAt 2729 (.Dup ⟨1, by decide⟩),
   pushAt 2730 2 5120,
   opAt 2731 .ADD,
   opAt 2732 .MSTORE,
   opAt 2733 (.Dup ⟨0, by decide⟩),
   opAt 2734 .ISZERO,
   pushAt 2735 2 4735,
   opAt 2736 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2737 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2738 .ADD,
   pushAt 2739 2 4674,
   opAt 2740 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2741 .JUMPDEST,
   opAt 2742 .POP,
   opAt 2743 .POP,
   pushAt 2744 0 0,
   opAt 2745 .MLOAD,
   opAt 2746 (.Dup ⟨0, by decide⟩),
   pushAt 2747 0 0,
   opAt 2748 .SUB,
   opAt 2749 (.Dup ⟨1, by decide⟩),
   opAt 2750 .AND,
   opAt 2751 (.Dup ⟨0, by decide⟩),
   pushAt 2752 2 6144,
   opAt 2753 .MSTORE,
   opAt 2754 (.Dup ⟨0, by decide⟩),
   opAt 2755 (.Dup ⟨2, by decide⟩),
   opAt 2756 .DIV,
   opAt 2757 (.Dup ⟨0, by decide⟩),
   pushAt 2758 2 6176,
   opAt 2759 .MSTORE,
   opAt 2760 (.Dup ⟨1, by decide⟩),
   pushAt 2761 0 0,
   opAt 2762 .SUB,
   opAt 2763 (.Dup ⟨2, by decide⟩),
   opAt 2764 (.Swap ⟨0, by decide⟩),
   opAt 2765 .DIV,
   pushAt 2766 1 1,
   opAt 2767 .ADD,
   pushAt 2768 2 6208,
   opAt 2769 .MSTORE,
   opAt 2770 (.Dup ⟨0, by decide⟩),
   pushAt 2771 0 0,
   opAt 2772 .SUB,
   opAt 2773 (.Dup ⟨1, by decide⟩),
   opAt 2774 (.Swap ⟨0, by decide⟩),
   opAt 2775 .MOD,
   pushAt 2776 2 6240,
   opAt 2777 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2778 .JUMPDEST,
   pushAt 2779 1 1,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   opAt 2781 (.Dup ⟨2, by decide⟩),
   opAt 2782 .MUL,
   pushAt 2783 1 2,
   opAt 2784 .SUB,
   opAt 2785 .MUL,
   opAt 2786 (.Dup ⟨0, by decide⟩),
   opAt 2787 (.Dup ⟨2, by decide⟩),
   opAt 2788 .MUL,
   pushAt 2789 1 2,
   opAt 2790 .SUB,
   opAt 2791 .MUL,
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
   opAt 2803 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2804 .JUMPDEST,
   opAt 2805 (.Dup ⟨0, by decide⟩),
   opAt 2806 (.Dup ⟨2, by decide⟩),
   opAt 2807 .MUL,
   pushAt 2808 1 2,
   opAt 2809 .SUB,
   opAt 2810 .MUL,
   opAt 2811 (.Dup ⟨0, by decide⟩),
   opAt 2812 (.Dup ⟨2, by decide⟩),
   opAt 2813 .MUL,
   pushAt 2814 1 2,
   opAt 2815 .SUB,
   opAt 2816 .MUL,
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
   pushAt 2829 2 6272,
   opAt 2830 .MSTORE,
   opAt 2831 .POP,
   opAt 2832 .POP,
   opAt 2833 .POP,
   opAt 2834 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2835 .JUMPDEST,
   opAt 2836 (.Dup ⟨0, by decide⟩),
   opAt 2837 .ISZERO,
   pushAt 2838 2 5345,
   opAt 2839 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2840 (.Dup ⟨1, by decide⟩),
   pushAt 2841 2 2048,
   pushAt 2842 2 8224,
   opAt 2843 .MCOPY,
   pushAt 2844 0 0,
   pushAt 2845 2 9440,
   opAt 2846 .MLOAD,
   opAt 2847 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2848 .JUMPDEST,
   pushAt 2849 2 2048,
   opAt 2850 .MLOAD,
   pushAt 2851 2 6144,
   opAt 2852 .MLOAD,
   opAt 2853 (.Dup ⟨1, by decide⟩),
   opAt 2854 (.Dup ⟨1, by decide⟩),
   opAt 2855 (.Swap ⟨0, by decide⟩),
   opAt 2856 .DIV,
   opAt 2857 (.Swap ⟨1, by decide⟩),
   opAt 2858 .MOD,
   pushAt 2859 2 6208,
   opAt 2860 .MLOAD,
   opAt 2861 .MUL,
   pushAt 2862 2 2080,
   opAt 2863 .MLOAD,
   pushAt 2864 2 6144,
   opAt 2865 .MLOAD,
   opAt 2866 (.Swap ⟨0, by decide⟩),
   opAt 2867 .DIV,
   opAt 2868 .ADD,
   pushAt 2869 2 6176,
   opAt 2870 .MLOAD,
   opAt 2871 (.Dup ⟨0, by decide⟩),
   pushAt 2872 2 6240,
   opAt 2873 .MLOAD,
   opAt 2874 (.Dup ⟨4, by decide⟩),
   opAt 2875 .MULMOD,
   opAt 2876 (.Dup ⟨2, by decide⟩),
   opAt 2877 (.Swap ⟨0, by decide⟩),
   opAt 2878 .ADDMOD,
   opAt 2879 (.Swap ⟨0, by decide⟩),
   opAt 2880 .SUB,
   pushAt 2881 2 6272,
   opAt 2882 .MLOAD,
   opAt 2883 .MUL,
   opAt 2884 (.Dup ⟨0, by decide⟩),
   pushAt 2885 0 0,
   opAt 2886 .LT,
   opAt 2887 (.Swap ⟨0, by decide⟩),
   opAt 2888 .SUB,
   opAt 2889 (.Swap ⟨0, by decide⟩),
   pushAt 2890 2 6176,
   opAt 2891 .MLOAD,
   opAt 2892 (.Swap ⟨0, by decide⟩),
   opAt 2893 .LT,
   opAt 2894 .ISZERO,
   pushAt 2895 0 0,
   opAt 2896 .SUB,
   opAt 2897 .OR]

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

/-- Instructions 3077..3124, pc 4968..5115. -/
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
   pushAt 2944 2 8224,
   opAt 2945 (.Dup ⟨2, by decide⟩),
   opAt 2946 .GT,
   pushAt 2947 2 4952,
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
   pushAt 2975 2 5226,
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
   pushAt 3014 2 5135,
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
   pushAt 3026 2 5129,
   opAt 3027 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3028 .JUMPDEST,
   pushAt 3029 2 8224,
   opAt 3030 .MLOAD,
   opAt 3031 .ISZERO,
   pushAt 3032 2 5325,
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
   pushAt 3067 2 5241,
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
   pushAt 3075 2 5226,
   opAt 3076 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3077 .JUMPDEST,
   pushAt 3078 2 5336,
   pushAt 3079 2 2048,
   pushAt 3080 2 2637,
   opAt 3081 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3082 .JUMPDEST,
   pushAt 3083 1 1,
   opAt 3084 (.Swap ⟨0, by decide⟩),
   opAt 3085 .SUB,
   pushAt 3086 2 4849,
   opAt 3087 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3088 .JUMPDEST,
   opAt 3089 .POP,
   pushAt 3090 2 1756,
   opAt 3091 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4618 = true :=
  Artifact.isValidJumpDest_index 2684 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4662 = true :=
  Artifact.isValidJumpDest_index 2711 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4667 = true :=
  Artifact.isValidJumpDest_index 2714 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4674 = true :=
  Artifact.isValidJumpDest_index 2718 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 2741 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4781 = true :=
  Artifact.isValidJumpDest_index 2778 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4812 = true :=
  Artifact.isValidJumpDest_index 2804 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4849 = true :=
  Artifact.isValidJumpDest_index 2835 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4870 = true :=
  Artifact.isValidJumpDest_index 2848 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4938 = true :=
  Artifact.isValidJumpDest_index 2898 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4952 = true :=
  Artifact.isValidJumpDest_index 2906 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5129 = true :=
  Artifact.isValidJumpDest_index 2977 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5135 = true :=
  Artifact.isValidJumpDest_index 2981 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5226 = true :=
  Artifact.isValidJumpDest_index 3028 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5241 = true :=
  Artifact.isValidJumpDest_index 3037 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5325 = true :=
  Artifact.isValidJumpDest_index 3077 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5336 = true :=
  Artifact.isValidJumpDest_index 3082 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5345 = true :=
  Artifact.isValidJumpDest_index 3088 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
