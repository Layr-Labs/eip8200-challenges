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
  [opAt 2676 .JUMPDEST,
   opAt 2677 (.Dup ⟨0, by decide⟩),
   opAt 2678 (.Dup ⟨3, by decide⟩),
   opAt 2679 .EQ,
   pushAt 2680 0 0,
   opAt 2681 .MLOAD,
   pushAt 2682 1 255,
   opAt 2683 .SHR,
   opAt 2684 .AND,
   opAt 2685 .ISZERO,
   pushAt 2686 2 4662,
   opAt 2687 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2688 (.Dup ⟨0, by decide⟩),
   pushAt 2689 1 96,
   pushAt 2690 2 1024,
   opAt 2691 .CALLDATACOPY,
   opAt 2692 (.Dup ⟨0, by decide⟩),
   pushAt 2693 1 96,
   pushAt 2694 2 8256,
   opAt 2695 .CALLDATACOPY,
   pushAt 2696 0 0,
   pushAt 2697 2 8224,
   opAt 2698 .MSTORE,
   pushAt 2699 2 4667,
   pushAt 2700 2 2048,
   pushAt 2701 2 2637,
   opAt 2702 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2703 .JUMPDEST,
   pushAt 2704 2 1533,
   opAt 2705 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2706 .JUMPDEST,
   pushAt 2707 1 1,
   pushAt 2708 2 9408,
   opAt 2709 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2710 .JUMPDEST,
   opAt 2711 (.Dup ⟨0, by decide⟩),
   opAt 2712 .MLOAD,
   opAt 2713 .NOT,
   opAt 2714 (.Dup ⟨2, by decide⟩),
   opAt 2715 .ADD,
   opAt 2716 (.Dup ⟨2, by decide⟩),
   opAt 2717 (.Dup ⟨1, by decide⟩),
   opAt 2718 .LT,
   opAt 2719 (.Swap ⟨2, by decide⟩),
   opAt 2720 .POP,
   opAt 2721 (.Dup ⟨1, by decide⟩),
   pushAt 2722 2 5120,
   opAt 2723 .ADD,
   opAt 2724 .MSTORE,
   opAt 2725 (.Dup ⟨0, by decide⟩),
   opAt 2726 .ISZERO,
   pushAt 2727 2 4735,
   opAt 2728 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2729 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2730 .ADD,
   pushAt 2731 2 4674,
   opAt 2732 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2733 .JUMPDEST,
   opAt 2734 .POP,
   opAt 2735 .POP,
   pushAt 2736 0 0,
   opAt 2737 .MLOAD,
   opAt 2738 (.Dup ⟨0, by decide⟩),
   pushAt 2739 0 0,
   opAt 2740 .SUB,
   opAt 2741 (.Dup ⟨1, by decide⟩),
   opAt 2742 .AND,
   opAt 2743 (.Dup ⟨0, by decide⟩),
   pushAt 2744 2 6144,
   opAt 2745 .MSTORE,
   opAt 2746 (.Dup ⟨0, by decide⟩),
   opAt 2747 (.Dup ⟨2, by decide⟩),
   opAt 2748 .DIV,
   opAt 2749 (.Dup ⟨0, by decide⟩),
   pushAt 2750 2 6176,
   opAt 2751 .MSTORE,
   opAt 2752 (.Dup ⟨1, by decide⟩),
   pushAt 2753 0 0,
   opAt 2754 .SUB,
   opAt 2755 (.Dup ⟨2, by decide⟩),
   opAt 2756 (.Swap ⟨0, by decide⟩),
   opAt 2757 .DIV,
   pushAt 2758 1 1,
   opAt 2759 .ADD,
   pushAt 2760 2 6208,
   opAt 2761 .MSTORE,
   opAt 2762 (.Dup ⟨0, by decide⟩),
   pushAt 2763 0 0,
   opAt 2764 .SUB,
   opAt 2765 (.Dup ⟨1, by decide⟩),
   opAt 2766 (.Swap ⟨0, by decide⟩),
   opAt 2767 .MOD,
   pushAt 2768 2 6240,
   opAt 2769 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2770 .JUMPDEST,
   pushAt 2771 1 1,
   opAt 2772 (.Dup ⟨0, by decide⟩),
   opAt 2773 (.Dup ⟨2, by decide⟩),
   opAt 2774 .MUL,
   pushAt 2775 1 2,
   opAt 2776 .SUB,
   opAt 2777 .MUL,
   opAt 2778 (.Dup ⟨0, by decide⟩),
   opAt 2779 (.Dup ⟨2, by decide⟩),
   opAt 2780 .MUL,
   pushAt 2781 1 2,
   opAt 2782 .SUB,
   opAt 2783 .MUL,
   opAt 2784 (.Dup ⟨0, by decide⟩),
   opAt 2785 (.Dup ⟨2, by decide⟩),
   opAt 2786 .MUL,
   pushAt 2787 1 2,
   opAt 2788 .SUB,
   opAt 2789 .MUL,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   opAt 2791 (.Dup ⟨2, by decide⟩),
   opAt 2792 .MUL,
   pushAt 2793 1 2,
   opAt 2794 .SUB,
   opAt 2795 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2796 .JUMPDEST,
   opAt 2797 (.Dup ⟨0, by decide⟩),
   opAt 2798 (.Dup ⟨2, by decide⟩),
   opAt 2799 .MUL,
   pushAt 2800 1 2,
   opAt 2801 .SUB,
   opAt 2802 .MUL,
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
   pushAt 2821 2 6272,
   opAt 2822 .MSTORE,
   opAt 2823 .POP,
   opAt 2824 .POP,
   opAt 2825 .POP,
   opAt 2826 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2827 .JUMPDEST,
   opAt 2828 (.Dup ⟨0, by decide⟩),
   opAt 2829 .ISZERO,
   pushAt 2830 2 5345,
   opAt 2831 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2832 (.Dup ⟨1, by decide⟩),
   pushAt 2833 2 2048,
   pushAt 2834 2 8224,
   opAt 2835 .MCOPY,
   pushAt 2836 0 0,
   pushAt 2837 2 9440,
   opAt 2838 .MLOAD,
   opAt 2839 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2840 .JUMPDEST,
   pushAt 2841 2 2048,
   opAt 2842 .MLOAD,
   pushAt 2843 2 6144,
   opAt 2844 .MLOAD,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 (.Swap ⟨0, by decide⟩),
   opAt 2848 .DIV,
   opAt 2849 (.Swap ⟨1, by decide⟩),
   opAt 2850 .MOD,
   pushAt 2851 2 6208,
   opAt 2852 .MLOAD,
   opAt 2853 .MUL,
   pushAt 2854 2 2080,
   opAt 2855 .MLOAD,
   pushAt 2856 2 6144,
   opAt 2857 .MLOAD,
   opAt 2858 (.Swap ⟨0, by decide⟩),
   opAt 2859 .DIV,
   opAt 2860 .ADD,
   pushAt 2861 2 6176,
   opAt 2862 .MLOAD,
   opAt 2863 (.Dup ⟨0, by decide⟩),
   pushAt 2864 2 6240,
   opAt 2865 .MLOAD,
   opAt 2866 (.Dup ⟨4, by decide⟩),
   opAt 2867 .MULMOD,
   opAt 2868 (.Dup ⟨2, by decide⟩),
   opAt 2869 .JUMPDEST,
   opAt 2870 .ADDMOD,
   opAt 2871 (.Swap ⟨0, by decide⟩),
   opAt 2872 .SUB,
   pushAt 2873 2 6272,
   opAt 2874 .MLOAD,
   opAt 2875 .MUL,
   opAt 2876 (.Dup ⟨0, by decide⟩),
   pushAt 2877 0 0,
   opAt 2878 .LT,
   opAt 2879 (.Swap ⟨0, by decide⟩),
   opAt 2880 .SUB,
   opAt 2881 (.Swap ⟨0, by decide⟩),
   pushAt 2882 2 6176,
   opAt 2883 .MLOAD,
   opAt 2884 .JUMPDEST,
   opAt 2885 .GT,
   opAt 2886 .ISZERO,
   pushAt 2887 0 0,
   opAt 2888 .SUB,
   opAt 2889 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2890 .JUMPDEST,
   pushAt 2891 0 0,
   pushAt 2892 2 9440,
   opAt 2893 .MLOAD,
   pushAt 2894 2 9408,
   opAt 2895 .MLOAD,
   pushAt 2896 2 5120,
   opAt 2897 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2898 .JUMPDEST,
   opAt 2899 (.Dup ⟨0, by decide⟩),
   opAt 2900 .MLOAD,
   pushAt 2901 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2902 (.Dup ⟨5, by decide⟩),
   opAt 2903 (.Dup ⟨2, by decide⟩),
   opAt 2904 .MUL,
   opAt 2905 (.Swap ⟨1, by decide⟩),
   opAt 2906 (.Dup ⟨6, by decide⟩),
   opAt 2907 .MULMOD,
   opAt 2908 (.Dup ⟨1, by decide⟩),
   opAt 2909 (.Dup ⟨1, by decide⟩),
   opAt 2910 .LT,
   opAt 2911 .SUB,
   opAt 2912 (.Dup ⟨4, by decide⟩),
   opAt 2913 (.Dup ⟨2, by decide⟩),
   opAt 2914 .ADD,
   opAt 2915 (.Dup ⟨0, by decide⟩),
   opAt 2916 (.Swap ⟨5, by decide⟩),
   opAt 2917 .GT,
   opAt 2918 .SUB,
   opAt 2919 .SUB,
   opAt 2920 (.Dup ⟨3, by decide⟩),
   opAt 2921 (.Dup ⟨3, by decide⟩),
   opAt 2922 .MLOAD,
   opAt 2923 .ADD,
   opAt 2924 (.Dup ⟨0, by decide⟩),
   opAt 2925 (.Swap ⟨4, by decide⟩),
   opAt 2926 .GT,
   opAt 2927 .ADD,
   opAt 2928 (.Swap ⟨2, by decide⟩),
   opAt 2929 (.Dup ⟨2, by decide⟩),
   pushAt 2930 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2931 .ADD,
   opAt 2932 (.Swap ⟨2, by decide⟩),
   opAt 2933 .MSTORE,
   pushAt 2934 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2935 .ADD,
   pushAt 2936 2 8224,
   opAt 2937 (.Dup ⟨2, by decide⟩),
   opAt 2938 .GT,
   pushAt 2939 2 4952,
   opAt 2940 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2941 .POP,
   opAt 2942 .POP,
   pushAt 2943 2 8224,
   opAt 2944 .MLOAD,
   opAt 2945 (.Dup ⟨1, by decide⟩),
   opAt 2946 .ADD,
   opAt 2947 (.Dup ⟨1, by decide⟩),
   opAt 2948 (.Dup ⟨1, by decide⟩),
   opAt 2949 .LT,
   opAt 2950 (.Swap ⟨1, by decide⟩),
   opAt 2951 .POP,
   opAt 2952 (.Dup ⟨2, by decide⟩),
   opAt 2953 (.Dup ⟨1, by decide⟩),
   opAt 2954 .LT,
   opAt 2955 (.Swap ⟨0, by decide⟩),
   opAt 2956 (.Dup ⟨3, by decide⟩),
   opAt 2957 (.Swap ⟨0, by decide⟩),
   opAt 2958 .SUB,
   opAt 2959 (.Dup ⟨0, by decide⟩),
   pushAt 2960 2 8224,
   opAt 2961 .MSTORE,
   opAt 2962 .POP,
   opAt 2963 .GT,
   opAt 2964 (.Swap ⟨0, by decide⟩),
   opAt 2965 .POP,
   opAt 2966 .ISZERO,
   pushAt 2967 2 5226,
   opAt 2968 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2969 .JUMPDEST,
   pushAt 2970 0 0,
   pushAt 2971 2 9440,
   opAt 2972 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2973 .JUMPDEST,
   opAt 2974 (.Dup ⟨0, by decide⟩),
   opAt 2975 .MLOAD,
   opAt 2976 (.Dup ⟨1, by decide⟩),
   pushAt 2977 2 8256,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 .SUB,
   opAt 2980 .MLOAD,
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 .ADD,
   opAt 2983 (.Dup ⟨0, by decide⟩),
   opAt 2984 (.Dup ⟨2, by decide⟩),
   opAt 2985 .GT,
   opAt 2986 (.Swap ⟨1, by decide⟩),
   opAt 2987 .POP,
   opAt 2988 (.Dup ⟨3, by decide⟩),
   opAt 2989 .ADD,
   opAt 2990 (.Dup ⟨0, by decide⟩),
   opAt 2991 (.Dup ⟨4, by decide⟩),
   opAt 2992 .GT,
   opAt 2993 (.Swap ⟨3, by decide⟩),
   opAt 2994 .POP,
   opAt 2995 (.Dup ⟨2, by decide⟩),
   opAt 2996 .MSTORE,
   opAt 2997 (.Swap ⟨0, by decide⟩),
   opAt 2998 (.Swap ⟨1, by decide⟩),
   opAt 2999 .OR,
   opAt 3000 (.Swap ⟨0, by decide⟩),
   pushAt 3001 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3002 .ADD,
   pushAt 3003 2 8255,
   opAt 3004 (.Dup ⟨1, by decide⟩),
   opAt 3005 .GT,
   pushAt 3006 2 5135,
   opAt 3007 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3008 .POP,
   pushAt 3009 2 8224,
   opAt 3010 .MLOAD,
   opAt 3011 (.Dup ⟨1, by decide⟩),
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   pushAt 3014 2 8224,
   opAt 3015 .MSTORE,
   opAt 3016 .LT,
   opAt 3017 .ISZERO,
   pushAt 3018 2 5129,
   opAt 3019 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3020 .JUMPDEST,
   pushAt 3021 2 8224,
   opAt 3022 .MLOAD,
   opAt 3023 .ISZERO,
   pushAt 3024 2 5325,
   opAt 3025 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3026 0 0,
   pushAt 3027 2 9440,
   opAt 3028 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3029 .JUMPDEST,
   opAt 3030 (.Dup ⟨0, by decide⟩),
   opAt 3031 .MLOAD,
   opAt 3032 (.Dup ⟨1, by decide⟩),
   pushAt 3033 2 8256,
   opAt 3034 (.Swap ⟨0, by decide⟩),
   opAt 3035 .SUB,
   opAt 3036 .MLOAD,
   opAt 3037 (.Dup ⟨1, by decide⟩),
   opAt 3038 (.Dup ⟨1, by decide⟩),
   opAt 3039 .GT,
   opAt 3040 (.Swap ⟨1, by decide⟩),
   opAt 3041 .SUB,
   opAt 3042 (.Dup ⟨3, by decide⟩),
   opAt 3043 (.Dup ⟨1, by decide⟩),
   opAt 3044 .LT,
   opAt 3045 (.Swap ⟨0, by decide⟩),
   opAt 3046 (.Dup ⟨4, by decide⟩),
   opAt 3047 (.Swap ⟨0, by decide⟩),
   opAt 3048 .SUB,
   opAt 3049 (.Dup ⟨3, by decide⟩),
   opAt 3050 .MSTORE,
   opAt 3051 .OR,
   opAt 3052 (.Swap ⟨1, by decide⟩),
   opAt 3053 .POP,
   pushAt 3054 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3055 .ADD,
   pushAt 3056 2 8255,
   opAt 3057 (.Dup ⟨1, by decide⟩),
   opAt 3058 .GT,
   pushAt 3059 2 5241,
   opAt 3060 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3061 .POP,
   pushAt 3062 2 8224,
   opAt 3063 .MLOAD,
   opAt 3064 .SUB,
   pushAt 3065 2 8224,
   opAt 3066 .MSTORE,
   pushAt 3067 2 5226,
   opAt 3068 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3069 .JUMPDEST,
   pushAt 3070 2 5336,
   pushAt 3071 2 2048,
   pushAt 3072 2 2637,
   opAt 3073 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3074 .JUMPDEST,
   pushAt 3075 1 1,
   opAt 3076 (.Swap ⟨0, by decide⟩),
   opAt 3077 .SUB,
   pushAt 3078 2 4849,
   opAt 3079 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3080 .JUMPDEST,
   opAt 3081 .POP,
   pushAt 3082 2 1756,
   opAt 3083 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4618 = true :=
  Artifact.isValidJumpDest_index 2676 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4662 = true :=
  Artifact.isValidJumpDest_index 2703 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4667 = true :=
  Artifact.isValidJumpDest_index 2706 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4674 = true :=
  Artifact.isValidJumpDest_index 2710 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 2733 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4781 = true :=
  Artifact.isValidJumpDest_index 2770 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4812 = true :=
  Artifact.isValidJumpDest_index 2796 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4849 = true :=
  Artifact.isValidJumpDest_index 2827 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4870 = true :=
  Artifact.isValidJumpDest_index 2840 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4938 = true :=
  Artifact.isValidJumpDest_index 2890 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4952 = true :=
  Artifact.isValidJumpDest_index 2898 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5129 = true :=
  Artifact.isValidJumpDest_index 2969 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5135 = true :=
  Artifact.isValidJumpDest_index 2973 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5226 = true :=
  Artifact.isValidJumpDest_index 3020 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5241 = true :=
  Artifact.isValidJumpDest_index 3029 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5325 = true :=
  Artifact.isValidJumpDest_index 3069 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5336 = true :=
  Artifact.isValidJumpDest_index 3074 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5345 = true :=
  Artifact.isValidJumpDest_index 3080 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
