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
  [opAt 2675 .JUMPDEST,
   opAt 2676 (.Dup ⟨0, by decide⟩),
   opAt 2677 (.Dup ⟨3, by decide⟩),
   opAt 2678 .EQ,
   pushAt 2679 0 0,
   opAt 2680 .MLOAD,
   pushAt 2681 1 255,
   opAt 2682 .SHR,
   opAt 2683 .AND,
   opAt 2684 .ISZERO,
   pushAt 2685 2 4662,
   opAt 2686 .JUMPI]

/-- Instructions 2874..2888, pc 4658..4686. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2687 (.Dup ⟨0, by decide⟩),
   pushAt 2688 1 96,
   pushAt 2689 2 1024,
   opAt 2690 .CALLDATACOPY,
   opAt 2691 (.Dup ⟨0, by decide⟩),
   pushAt 2692 1 96,
   pushAt 2693 2 8256,
   opAt 2694 .CALLDATACOPY,
   pushAt 2695 0 0,
   pushAt 2696 2 8224,
   opAt 2697 .MSTORE,
   pushAt 2698 2 4667,
   pushAt 2699 2 2048,
   pushAt 2700 2 2637,
   opAt 2701 .JUMP]

/-- Instructions 2889..2891, pc 4687..4691. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2702 .JUMPDEST,
   pushAt 2703 2 1533,
   opAt 2704 .JUMP]

/-- Instructions 2892..2895, pc 4692..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2705 .JUMPDEST,
   pushAt 2706 1 1,
   pushAt 2707 2 9408,
   opAt 2708 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2709 .JUMPDEST,
   opAt 2710 (.Dup ⟨0, by decide⟩),
   opAt 2711 .MLOAD,
   opAt 2712 .NOT,
   opAt 2713 (.Dup ⟨2, by decide⟩),
   opAt 2714 .ADD,
   opAt 2715 (.Dup ⟨2, by decide⟩),
   opAt 2716 (.Dup ⟨1, by decide⟩),
   opAt 2717 .LT,
   opAt 2718 (.Swap ⟨2, by decide⟩),
   opAt 2719 .POP,
   opAt 2720 (.Dup ⟨1, by decide⟩),
   pushAt 2721 2 5120,
   opAt 2722 .ADD,
   opAt 2723 .MSTORE,
   opAt 2724 (.Dup ⟨0, by decide⟩),
   opAt 2725 .ISZERO,
   pushAt 2726 2 4735,
   opAt 2727 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4759. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2728 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2729 .ADD,
   pushAt 2730 2 4674,
   opAt 2731 .JUMP]

/-- Instructions 2919..2955, pc 4760..4805. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2732 .JUMPDEST,
   opAt 2733 .POP,
   opAt 2734 .POP,
   pushAt 2735 0 0,
   opAt 2736 .MLOAD,
   opAt 2737 (.Dup ⟨0, by decide⟩),
   pushAt 2738 0 0,
   opAt 2739 .SUB,
   opAt 2740 (.Dup ⟨1, by decide⟩),
   opAt 2741 .AND,
   opAt 2742 (.Dup ⟨0, by decide⟩),
   pushAt 2743 2 6144,
   opAt 2744 .MSTORE,
   opAt 2745 (.Dup ⟨0, by decide⟩),
   opAt 2746 (.Dup ⟨2, by decide⟩),
   opAt 2747 .DIV,
   opAt 2748 (.Dup ⟨0, by decide⟩),
   pushAt 2749 2 6176,
   opAt 2750 .MSTORE,
   opAt 2751 (.Dup ⟨1, by decide⟩),
   pushAt 2752 0 0,
   opAt 2753 .SUB,
   opAt 2754 (.Dup ⟨2, by decide⟩),
   opAt 2755 (.Swap ⟨0, by decide⟩),
   opAt 2756 .DIV,
   pushAt 2757 1 1,
   opAt 2758 .ADD,
   pushAt 2759 2 6208,
   opAt 2760 .MSTORE,
   opAt 2761 (.Dup ⟨0, by decide⟩),
   pushAt 2762 0 0,
   opAt 2763 .SUB,
   opAt 2764 (.Dup ⟨1, by decide⟩),
   opAt 2765 (.Swap ⟨0, by decide⟩),
   opAt 2766 .MOD,
   pushAt 2767 2 6240,
   opAt 2768 .MSTORE]

/-- Instructions 2956..2981, pc 4806..4836. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2769 .JUMPDEST,
   pushAt 2770 1 1,
   opAt 2771 (.Dup ⟨0, by decide⟩),
   opAt 2772 (.Dup ⟨2, by decide⟩),
   opAt 2773 .MUL,
   pushAt 2774 1 2,
   opAt 2775 .SUB,
   opAt 2776 .MUL,
   opAt 2777 (.Dup ⟨0, by decide⟩),
   opAt 2778 (.Dup ⟨2, by decide⟩),
   opAt 2779 .MUL,
   pushAt 2780 1 2,
   opAt 2781 .SUB,
   opAt 2782 .MUL,
   opAt 2783 (.Dup ⟨0, by decide⟩),
   opAt 2784 (.Dup ⟨2, by decide⟩),
   opAt 2785 .MUL,
   pushAt 2786 1 2,
   opAt 2787 .SUB,
   opAt 2788 .MUL,
   opAt 2789 (.Dup ⟨0, by decide⟩),
   opAt 2790 (.Dup ⟨2, by decide⟩),
   opAt 2791 .MUL,
   pushAt 2792 1 2,
   opAt 2793 .SUB,
   opAt 2794 .MUL]

/-- Instructions 2982..3012, pc 4837..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2795 .JUMPDEST,
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
   opAt 2813 .MUL,
   opAt 2814 (.Dup ⟨0, by decide⟩),
   opAt 2815 (.Dup ⟨2, by decide⟩),
   opAt 2816 .MUL,
   pushAt 2817 1 2,
   opAt 2818 .SUB,
   opAt 2819 .MUL,
   pushAt 2820 2 6272,
   opAt 2821 .MSTORE,
   opAt 2822 .POP,
   opAt 2823 .POP,
   opAt 2824 .POP,
   opAt 2825 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4874..4880. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2826 .JUMPDEST,
   opAt 2827 (.Dup ⟨0, by decide⟩),
   opAt 2828 .ISZERO,
   pushAt 2829 2 5345,
   opAt 2830 .JUMPI]

/-- Instructions 3018..3025, pc 4881..4894. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2831 (.Dup ⟨1, by decide⟩),
   pushAt 2832 2 2048,
   pushAt 2833 2 8224,
   opAt 2834 .MCOPY,
   pushAt 2835 0 0,
   pushAt 2836 2 9440,
   opAt 2837 .MLOAD,
   opAt 2838 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4953. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2839 .JUMPDEST,
   pushAt 2840 2 2048,
   opAt 2841 .MLOAD,
   pushAt 2842 2 6144,
   opAt 2843 .MLOAD,
   opAt 2844 (.Dup ⟨1, by decide⟩),
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 (.Swap ⟨0, by decide⟩),
   opAt 2847 .DIV,
   opAt 2848 (.Swap ⟨1, by decide⟩),
   opAt 2849 .MOD,
   pushAt 2850 2 6208,
   opAt 2851 .MLOAD,
   opAt 2852 .MUL,
   pushAt 2853 2 2080,
   opAt 2854 .MLOAD,
   pushAt 2855 2 6144,
   opAt 2856 .MLOAD,
   opAt 2857 (.Swap ⟨0, by decide⟩),
   opAt 2858 .DIV,
   opAt 2859 .ADD,
   pushAt 2860 2 6176,
   opAt 2861 .MLOAD,
   opAt 2862 (.Dup ⟨0, by decide⟩),
   pushAt 2863 2 6240,
   opAt 2864 .MLOAD,
   opAt 2865 (.Dup ⟨4, by decide⟩),
   opAt 2866 .MULMOD,
   opAt 2867 (.Dup ⟨2, by decide⟩),
   opAt 2868 (.Swap ⟨0, by decide⟩),
   opAt 2869 .ADDMOD,
   opAt 2870 (.Swap ⟨0, by decide⟩),
   opAt 2871 .SUB,
   pushAt 2872 2 6272,
   opAt 2873 .MLOAD,
   opAt 2874 .MUL,
   opAt 2875 (.Dup ⟨0, by decide⟩),
   pushAt 2876 0 0,
   opAt 2877 .LT,
   opAt 2878 (.Swap ⟨0, by decide⟩),
   opAt 2879 .SUB,
   opAt 2880 (.Swap ⟨0, by decide⟩),
   pushAt 2881 2 6176,
   opAt 2882 .MLOAD,
   opAt 2883 .JUMPDEST,
   opAt 2884 .GT,
   opAt 2885 .ISZERO,
   pushAt 2886 0 0,
   opAt 2887 .SUB,
   opAt 2888 .OR]

/-- Instructions 3069..3076, pc 4954..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2889 .JUMPDEST,
   pushAt 2890 0 0,
   pushAt 2891 2 9440,
   opAt 2892 .MLOAD,
   pushAt 2893 2 9408,
   opAt 2894 .MLOAD,
   pushAt 2895 2 5120,
   opAt 2896 .ADD]

/-- Instructions 3077..3124, pc 4968..5115. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2897 .JUMPDEST,
   opAt 2898 (.Dup ⟨0, by decide⟩),
   opAt 2899 .MLOAD,
   pushAt 2900 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2901 (.Dup ⟨5, by decide⟩),
   opAt 2902 (.Dup ⟨2, by decide⟩),
   opAt 2903 .MUL,
   opAt 2904 (.Swap ⟨1, by decide⟩),
   opAt 2905 (.Dup ⟨6, by decide⟩),
   opAt 2906 .MULMOD,
   opAt 2907 (.Dup ⟨1, by decide⟩),
   opAt 2908 (.Dup ⟨1, by decide⟩),
   opAt 2909 .LT,
   opAt 2910 .SUB,
   opAt 2911 (.Dup ⟨4, by decide⟩),
   opAt 2912 (.Dup ⟨2, by decide⟩),
   opAt 2913 .ADD,
   opAt 2914 (.Dup ⟨0, by decide⟩),
   opAt 2915 (.Swap ⟨5, by decide⟩),
   opAt 2916 .GT,
   opAt 2917 .SUB,
   opAt 2918 .SUB,
   opAt 2919 (.Dup ⟨3, by decide⟩),
   opAt 2920 (.Dup ⟨3, by decide⟩),
   opAt 2921 .MLOAD,
   opAt 2922 .ADD,
   opAt 2923 (.Dup ⟨0, by decide⟩),
   opAt 2924 (.Swap ⟨4, by decide⟩),
   opAt 2925 .GT,
   opAt 2926 .ADD,
   opAt 2927 (.Swap ⟨2, by decide⟩),
   opAt 2928 (.Dup ⟨2, by decide⟩),
   pushAt 2929 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2930 .ADD,
   opAt 2931 (.Swap ⟨2, by decide⟩),
   opAt 2932 .MSTORE,
   pushAt 2933 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2934 .ADD,
   pushAt 2935 2 8224,
   opAt 2936 (.Dup ⟨2, by decide⟩),
   opAt 2937 .GT,
   pushAt 2938 2 4952,
   opAt 2939 .JUMPI]

/-- Instructions 3125..3152, pc 5116..5149. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2940 .POP,
   opAt 2941 .POP,
   pushAt 2942 2 8224,
   opAt 2943 .MLOAD,
   opAt 2944 (.Dup ⟨1, by decide⟩),
   opAt 2945 .ADD,
   opAt 2946 (.Dup ⟨1, by decide⟩),
   opAt 2947 (.Dup ⟨1, by decide⟩),
   opAt 2948 .LT,
   opAt 2949 (.Swap ⟨1, by decide⟩),
   opAt 2950 .POP,
   opAt 2951 (.Dup ⟨2, by decide⟩),
   opAt 2952 (.Dup ⟨1, by decide⟩),
   opAt 2953 .LT,
   opAt 2954 (.Swap ⟨0, by decide⟩),
   opAt 2955 (.Dup ⟨3, by decide⟩),
   opAt 2956 (.Swap ⟨0, by decide⟩),
   opAt 2957 .SUB,
   opAt 2958 (.Dup ⟨0, by decide⟩),
   pushAt 2959 2 8224,
   opAt 2960 .MSTORE,
   opAt 2961 .POP,
   opAt 2962 .GT,
   opAt 2963 (.Swap ⟨0, by decide⟩),
   opAt 2964 .POP,
   opAt 2965 .ISZERO,
   pushAt 2966 2 5226,
   opAt 2967 .JUMPI]

/-- Instructions 3153..3156, pc 5150..5155. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2968 .JUMPDEST,
   pushAt 2969 0 0,
   pushAt 2970 2 9440,
   opAt 2971 .MLOAD]

/-- Instructions 3157..3191, pc 5156..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2972 .JUMPDEST,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 .MLOAD,
   opAt 2975 (.Dup ⟨1, by decide⟩),
   pushAt 2976 2 8256,
   opAt 2977 (.Swap ⟨0, by decide⟩),
   opAt 2978 .SUB,
   opAt 2979 .MLOAD,
   opAt 2980 (.Dup ⟨1, by decide⟩),
   opAt 2981 .ADD,
   opAt 2982 (.Dup ⟨0, by decide⟩),
   opAt 2983 (.Dup ⟨2, by decide⟩),
   opAt 2984 .GT,
   opAt 2985 (.Swap ⟨1, by decide⟩),
   opAt 2986 .POP,
   opAt 2987 (.Dup ⟨3, by decide⟩),
   opAt 2988 .ADD,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   opAt 2990 (.Dup ⟨4, by decide⟩),
   opAt 2991 .GT,
   opAt 2992 (.Swap ⟨3, by decide⟩),
   opAt 2993 .POP,
   opAt 2994 (.Dup ⟨2, by decide⟩),
   opAt 2995 .MSTORE,
   opAt 2996 (.Swap ⟨0, by decide⟩),
   opAt 2997 (.Swap ⟨1, by decide⟩),
   opAt 2998 .OR,
   opAt 2999 (.Swap ⟨0, by decide⟩),
   pushAt 3000 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3001 .ADD,
   pushAt 3002 2 8255,
   opAt 3003 (.Dup ⟨1, by decide⟩),
   opAt 3004 .GT,
   pushAt 3005 2 5135,
   opAt 3006 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3007 .POP,
   pushAt 3008 2 8224,
   opAt 3009 .MLOAD,
   opAt 3010 (.Dup ⟨1, by decide⟩),
   opAt 3011 .ADD,
   opAt 3012 (.Dup ⟨0, by decide⟩),
   pushAt 3013 2 8224,
   opAt 3014 .MSTORE,
   opAt 3015 .LT,
   opAt 3016 .ISZERO,
   pushAt 3017 2 5129,
   opAt 3018 .JUMPI]

/-- Instructions 3204..3209, pc 5247..5256. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3019 .JUMPDEST,
   pushAt 3020 2 8224,
   opAt 3021 .MLOAD,
   opAt 3022 .ISZERO,
   pushAt 3023 2 5325,
   opAt 3024 .JUMPI]

/-- Instructions 3210..3212, pc 5257..5261. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3025 0 0,
   pushAt 3026 2 9440,
   opAt 3027 .MLOAD]

/-- Instructions 3213..3244, pc 5262..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3028 .JUMPDEST,
   opAt 3029 (.Dup ⟨0, by decide⟩),
   opAt 3030 .MLOAD,
   opAt 3031 (.Dup ⟨1, by decide⟩),
   pushAt 3032 2 8256,
   opAt 3033 (.Swap ⟨0, by decide⟩),
   opAt 3034 .SUB,
   opAt 3035 .MLOAD,
   opAt 3036 (.Dup ⟨1, by decide⟩),
   opAt 3037 (.Dup ⟨1, by decide⟩),
   opAt 3038 .GT,
   opAt 3039 (.Swap ⟨1, by decide⟩),
   opAt 3040 .SUB,
   opAt 3041 (.Dup ⟨3, by decide⟩),
   opAt 3042 (.Dup ⟨1, by decide⟩),
   opAt 3043 .LT,
   opAt 3044 (.Swap ⟨0, by decide⟩),
   opAt 3045 (.Dup ⟨4, by decide⟩),
   opAt 3046 (.Swap ⟨0, by decide⟩),
   opAt 3047 .SUB,
   opAt 3048 (.Dup ⟨3, by decide⟩),
   opAt 3049 .MSTORE,
   opAt 3050 .OR,
   opAt 3051 (.Swap ⟨1, by decide⟩),
   opAt 3052 .POP,
   pushAt 3053 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 3054 .ADD,
   pushAt 3055 2 8255,
   opAt 3056 (.Dup ⟨1, by decide⟩),
   opAt 3057 .GT,
   pushAt 3058 2 5241,
   opAt 3059 .JUMPI]

/-- Instructions 3245..3252, pc 5332..5345. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3060 .POP,
   pushAt 3061 2 8224,
   opAt 3062 .MLOAD,
   opAt 3063 .SUB,
   pushAt 3064 2 8224,
   opAt 3065 .MSTORE,
   pushAt 3066 2 5226,
   opAt 3067 .JUMP]

/-- Instructions 3253..3257, pc 5346..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3068 .JUMPDEST,
   pushAt 3069 2 5336,
   pushAt 3070 2 2048,
   pushAt 3071 2 2637,
   opAt 3072 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3073 .JUMPDEST,
   pushAt 3074 1 1,
   opAt 3075 (.Swap ⟨0, by decide⟩),
   opAt 3076 .SUB,
   pushAt 3077 2 4849,
   opAt 3078 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3079 .JUMPDEST,
   opAt 3080 .POP,
   pushAt 3081 2 1756,
   opAt 3082 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4618 = true :=
  Artifact.isValidJumpDest_index 2675 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4662 = true :=
  Artifact.isValidJumpDest_index 2702 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4667 = true :=
  Artifact.isValidJumpDest_index 2705 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4674 = true :=
  Artifact.isValidJumpDest_index 2709 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4735 = true :=
  Artifact.isValidJumpDest_index 2732 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4781 = true :=
  Artifact.isValidJumpDest_index 2769 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4812 = true :=
  Artifact.isValidJumpDest_index 2795 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4849 = true :=
  Artifact.isValidJumpDest_index 2826 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4870 = true :=
  Artifact.isValidJumpDest_index 2839 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4938 = true :=
  Artifact.isValidJumpDest_index 2889 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4952 = true :=
  Artifact.isValidJumpDest_index 2897 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5129 = true :=
  Artifact.isValidJumpDest_index 2968 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5135 = true :=
  Artifact.isValidJumpDest_index 2972 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5226 = true :=
  Artifact.isValidJumpDest_index 3019 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5241 = true :=
  Artifact.isValidJumpDest_index 3028 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5325 = true :=
  Artifact.isValidJumpDest_index 3068 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5336 = true :=
  Artifact.isValidJumpDest_index 3073 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5345 = true :=
  Artifact.isValidJumpDest_index 3079 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
