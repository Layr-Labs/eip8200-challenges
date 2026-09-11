import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block of the selected shift-reduce program. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2653 .JUMPDEST,
   opAt 2654 (.Dup ⟨0, by decide⟩),
   opAt 2655 (.Dup ⟨3, by decide⟩),
   opAt 2656 .EQ,
   pushAt 2657 0 0,
   opAt 2658 .MLOAD,
   pushAt 2659 1 255,
   opAt 2660 .SHR,
   opAt 2661 .AND,
   opAt 2662 .ISZERO,
   pushAt 2663 2 3540,
   opAt 2664 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2665 (.Dup ⟨0, by decide⟩),
   pushAt 2666 1 96,
   pushAt 2667 2 1024,
   opAt 2668 .CALLDATACOPY,
   opAt 2669 (.Dup ⟨0, by decide⟩),
   pushAt 2670 1 96,
   pushAt 2671 2 8256,
   opAt 2672 .CALLDATACOPY,
   pushAt 2673 0 0,
   pushAt 2674 2 8224,
   opAt 2675 .MSTORE,
   pushAt 2676 2 3545,
   pushAt 2677 2 2048,
   pushAt 2678 2 3815,
   opAt 2679 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2680 .JUMPDEST,
   pushAt 2681 2 1445,
   opAt 2682 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2683 .JUMPDEST,
   pushAt 2684 1 1,
   pushAt 2685 2 9408,
   opAt 2686 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2687 .JUMPDEST,
   opAt 2688 (.Dup ⟨0, by decide⟩),
   opAt 2689 .MLOAD,
   opAt 2690 .NOT,
   opAt 2691 (.Dup ⟨2, by decide⟩),
   opAt 2692 .ADD,
   opAt 2693 (.Dup ⟨2, by decide⟩),
   opAt 2694 (.Dup ⟨1, by decide⟩),
   opAt 2695 .LT,
   opAt 2696 (.Swap ⟨2, by decide⟩),
   opAt 2697 .POP,
   opAt 2698 (.Dup ⟨1, by decide⟩),
   pushAt 2699 2 5120,
   opAt 2700 .ADD,
   opAt 2701 .MSTORE,
   opAt 2702 (.Dup ⟨0, by decide⟩),
   opAt 2703 .ISZERO,
   pushAt 2704 2 3583,
   opAt 2705 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2706 1 31,
   opAt 2707 .NOT,
   opAt 2708 .ADD,
   pushAt 2709 2 3552,
   opAt 2710 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2711 .JUMPDEST,
   opAt 2712 .POP,
   opAt 2713 .POP,
   pushAt 2714 0 0,
   opAt 2715 .MLOAD,
   opAt 2716 (.Dup ⟨0, by decide⟩),
   pushAt 2717 0 0,
   opAt 2718 .SUB,
   opAt 2719 (.Dup ⟨1, by decide⟩),
   opAt 2720 .AND,
   opAt 2721 (.Dup ⟨0, by decide⟩),
   pushAt 2722 2 6144,
   opAt 2723 .MSTORE,
   opAt 2724 (.Dup ⟨0, by decide⟩),
   opAt 2725 (.Dup ⟨2, by decide⟩),
   opAt 2726 .DIV,
   opAt 2727 (.Dup ⟨0, by decide⟩),
   pushAt 2728 2 6176,
   opAt 2729 .MSTORE,
   opAt 2730 (.Dup ⟨1, by decide⟩),
   pushAt 2731 0 0,
   opAt 2732 .SUB,
   opAt 2733 (.Dup ⟨2, by decide⟩),
   opAt 2734 (.Swap ⟨0, by decide⟩),
   opAt 2735 .DIV,
   pushAt 2736 1 1,
   opAt 2737 .ADD,
   pushAt 2738 2 6208,
   opAt 2739 .MSTORE,
   opAt 2740 (.Dup ⟨0, by decide⟩),
   pushAt 2741 0 0,
   opAt 2742 .SUB,
   opAt 2743 (.Dup ⟨1, by decide⟩),
   opAt 2744 (.Swap ⟨0, by decide⟩),
   opAt 2745 .MOD,
   pushAt 2746 2 6240,
   opAt 2747 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2748 (.Dup ⟨0, by decide⟩),
   pushAt 2749 1 2,
   opAt 2750 .SUB,
   opAt 2751 (.Dup ⟨0, by decide⟩),
   opAt 2752 (.Dup ⟨2, by decide⟩),
   opAt 2753 .MUL,
   pushAt 2754 1 2,
   opAt 2755 .SUB,
   opAt 2756 .MUL,
   opAt 2757 (.Dup ⟨0, by decide⟩),
   opAt 2758 (.Dup ⟨2, by decide⟩),
   opAt 2759 .MUL,
   pushAt 2760 1 2,
   opAt 2761 .SUB,
   opAt 2762 .MUL,
   opAt 2763 (.Dup ⟨0, by decide⟩),
   opAt 2764 (.Dup ⟨2, by decide⟩),
   opAt 2765 .MUL,
   pushAt 2766 1 2,
   opAt 2767 .SUB,
   opAt 2768 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2769 (.Dup ⟨0, by decide⟩),
   opAt 2770 (.Dup ⟨2, by decide⟩),
   opAt 2771 .MUL,
   pushAt 2772 1 2,
   opAt 2773 .SUB,
   opAt 2774 .MUL,
   opAt 2775 (.Dup ⟨0, by decide⟩),
   opAt 2776 (.Dup ⟨2, by decide⟩),
   opAt 2777 .MUL,
   pushAt 2778 1 2,
   opAt 2779 .SUB,
   opAt 2780 .MUL,
   opAt 2781 (.Dup ⟨0, by decide⟩),
   opAt 2782 (.Dup ⟨2, by decide⟩),
   opAt 2783 .MUL,
   pushAt 2784 1 2,
   opAt 2785 .SUB,
   opAt 2786 .MUL,
   opAt 2787 (.Dup ⟨0, by decide⟩),
   opAt 2788 (.Dup ⟨2, by decide⟩),
   opAt 2789 .MUL,
   pushAt 2790 1 2,
   opAt 2791 .SUB,
   opAt 2792 .MUL,
   pushAt 2793 2 6272,
   opAt 2794 .MSTORE,
   opAt 2795 .POP,
   opAt 2796 .POP,
   opAt 2797 .POP,
   opAt 2798 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2799 .JUMPDEST,
   opAt 2800 (.Dup ⟨0, by decide⟩),
   opAt 2801 .ISZERO,
   pushAt 2802 2 4138,
   opAt 2803 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2804 (.Dup ⟨1, by decide⟩),
   pushAt 2805 2 2048,
   pushAt 2806 2 8224,
   opAt 2807 .MCOPY,
   pushAt 2808 0 0,
   pushAt 2809 2 9440,
   opAt 2810 .MLOAD,
   opAt 2811 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2812 2 2048,
   opAt 2813 .MLOAD,
   pushAt 2814 2 6144,
   opAt 2815 .MLOAD,
   opAt 2816 (.Dup ⟨0, by decide⟩),
   opAt 2817 (.Dup ⟨2, by decide⟩),
   opAt 2818 .DIV,
   opAt 2819 (.Swap ⟨1, by decide⟩),
   opAt 2820 .MOD,
   pushAt 2821 2 6208,
   opAt 2822 .MLOAD,
   opAt 2823 .MUL,
   pushAt 2824 2 2080,
   opAt 2825 .MLOAD,
   pushAt 2826 2 6144,
   opAt 2827 .MLOAD,
   opAt 2828 (.Swap ⟨0, by decide⟩),
   opAt 2829 .DIV,
   opAt 2830 .ADD,
   pushAt 2831 2 6176,
   opAt 2832 .MLOAD,
   opAt 2833 (.Dup ⟨0, by decide⟩),
   pushAt 2834 2 6240,
   opAt 2835 .MLOAD,
   opAt 2836 (.Dup ⟨4, by decide⟩),
   opAt 2837 .MULMOD,
   opAt 2838 (.Dup ⟨2, by decide⟩),
   opAt 2839 .ADDMOD,
   opAt 2840 (.Swap ⟨0, by decide⟩),
   opAt 2841 .SUB,
   pushAt 2842 2 6272,
   opAt 2843 .MLOAD,
   opAt 2844 .MUL,
   opAt 2845 (.Dup ⟨0, by decide⟩),
   pushAt 2846 0 0,
   opAt 2847 .MLOAD,
   opAt 2848 .MUL,
   pushAt 2849 2 2080,
   opAt 2850 .MLOAD,
   opAt 2851 .SUB,
   pushAt 2852 1 32,
   opAt 2853 .MLOAD,
   pushAt 2854 1 128,
   opAt 2855 .SHR,
   opAt 2856 (.Dup ⟨2, by decide⟩),
   pushAt 2857 1 128,
   opAt 2858 .SHR,
   opAt 2859 .MUL,
   opAt 2860 .GT,
   opAt 2861 (.Swap ⟨0, by decide⟩),
   opAt 2862 .SUB,
   opAt 2863 (.Swap ⟨0, by decide⟩),
   pushAt 2864 2 6176,
   opAt 2865 .MLOAD,
   opAt 2866 .GT,
   opAt 2867 .ISZERO,
   pushAt 2868 0 0,
   opAt 2869 .SUB,
   opAt 2870 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2871 0 0,
   pushAt 2872 2 9440,
   opAt 2873 .MLOAD,
   pushAt 2874 2 9408,
   opAt 2875 .MLOAD,
   pushAt 2876 2 5120,
   opAt 2877 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2878 .JUMPDEST,
   opAt 2879 (.Dup ⟨0, by decide⟩),
   opAt 2880 .MLOAD,
   pushAt 2881 0 0,
   opAt 2882 .NOT,
   pushAt 2883 2 3841,
   opAt 2884 .JUMP,
   opAt 2899 .JUMPDEST,
   opAt 2900 (.Dup ⟨5, by decide⟩),
   opAt 2901 (.Dup ⟨2, by decide⟩),
   opAt 2902 .MUL,
   opAt 2903 (.Swap ⟨1, by decide⟩),
   opAt 2904 (.Dup ⟨6, by decide⟩),
   opAt 2905 .MULMOD,
   opAt 2906 (.Dup ⟨1, by decide⟩),
   opAt 2907 (.Dup ⟨1, by decide⟩),
   opAt 2908 .LT,
   opAt 2909 .SUB,
   opAt 2910 (.Dup ⟨4, by decide⟩),
   opAt 2911 (.Dup ⟨2, by decide⟩),
   opAt 2912 .ADD,
   opAt 2913 (.Dup ⟨0, by decide⟩),
   opAt 2914 (.Swap ⟨5, by decide⟩),
   opAt 2915 .GT,
   opAt 2916 .SUB,
   opAt 2917 .SUB,
   opAt 2918 (.Dup ⟨3, by decide⟩),
   opAt 2919 (.Dup ⟨3, by decide⟩),
   opAt 2920 .MLOAD,
   opAt 2921 .ADD,
   opAt 2922 (.Dup ⟨0, by decide⟩),
   opAt 2923 (.Swap ⟨4, by decide⟩),
   opAt 2924 .GT,
   opAt 2925 .ADD,
   opAt 2926 (.Swap ⟨2, by decide⟩),
   opAt 2927 (.Dup ⟨2, by decide⟩),
   pushAt 2928 5 31,
   opAt 2929 .NOT,
   pushAt 2930 2 3902,
   opAt 2931 .JUMP,
   opAt 2946 .JUMPDEST,
   opAt 2947 .ADD,
   opAt 2948 (.Swap ⟨2, by decide⟩),
   opAt 2949 .MSTORE,
   pushAt 2950 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2951 .ADD,
   pushAt 2952 2 8224,
   opAt 2953 (.Dup ⟨2, by decide⟩),
   opAt 2954 .GT,
   pushAt 2955 2 3806,
   opAt 2956 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2957 .POP,
   opAt 2958 .POP,
   pushAt 2959 2 8224,
   opAt 2960 .MLOAD,
   opAt 2961 (.Dup ⟨1, by decide⟩),
   opAt 2962 .ADD,
   opAt 2963 (.Dup ⟨1, by decide⟩),
   opAt 2964 (.Dup ⟨1, by decide⟩),
   opAt 2965 .LT,
   opAt 2966 (.Swap ⟨1, by decide⟩),
   opAt 2967 .POP,
   opAt 2968 (.Dup ⟨2, by decide⟩),
   opAt 2969 (.Dup ⟨1, by decide⟩),
   opAt 2970 .LT,
   opAt 2971 (.Swap ⟨0, by decide⟩),
   opAt 2972 (.Dup ⟨3, by decide⟩),
   opAt 2973 (.Swap ⟨0, by decide⟩),
   opAt 2974 .SUB,
   opAt 2975 (.Dup ⟨0, by decide⟩),
   pushAt 2976 2 8224,
   opAt 2977 .MSTORE,
   opAt 2978 .POP,
   opAt 2979 .GT,
   opAt 2980 (.Swap ⟨0, by decide⟩),
   opAt 2981 .POP,
   opAt 2982 .ISZERO,
   pushAt 2983 2 4050,
   opAt 2984 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2985 .JUMPDEST,
   pushAt 2986 0 0,
   pushAt 2987 2 9440,
   opAt 2988 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2989 .JUMPDEST,
   opAt 2990 (.Dup ⟨0, by decide⟩),
   opAt 2991 .MLOAD,
   opAt 2992 (.Dup ⟨1, by decide⟩),
   pushAt 2993 2 8256,
   opAt 2994 (.Swap ⟨0, by decide⟩),
   opAt 2995 .SUB,
   opAt 2996 .MLOAD,
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 .ADD,
   opAt 2999 (.Dup ⟨0, by decide⟩),
   opAt 3000 (.Dup ⟨2, by decide⟩),
   opAt 3001 .GT,
   opAt 3002 (.Swap ⟨1, by decide⟩),
   opAt 3003 .POP,
   opAt 3004 (.Dup ⟨3, by decide⟩),
   opAt 3005 .ADD,
   opAt 3006 (.Dup ⟨0, by decide⟩),
   opAt 3007 (.Dup ⟨4, by decide⟩),
   opAt 3008 .GT,
   opAt 3009 (.Swap ⟨3, by decide⟩),
   opAt 3010 .POP,
   opAt 3011 (.Dup ⟨2, by decide⟩),
   opAt 3012 .MSTORE,
   opAt 3013 (.Swap ⟨0, by decide⟩),
   opAt 3014 (.Swap ⟨1, by decide⟩),
   opAt 3015 .OR,
   opAt 3016 (.Swap ⟨0, by decide⟩),
   pushAt 3017 1 31,
   opAt 3018 .NOT,
   opAt 3019 .ADD,
   pushAt 3020 2 8255,
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 .GT,
   pushAt 3023 2 3989,
   opAt 3024 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3025 .POP,
   pushAt 3026 2 8224,
   opAt 3027 .MLOAD,
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 .ADD,
   opAt 3030 (.Dup ⟨0, by decide⟩),
   pushAt 3031 2 8224,
   opAt 3032 .MSTORE,
   opAt 3033 .LT,
   opAt 3034 .ISZERO,
   pushAt 3035 2 3983,
   opAt 3036 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3037 .JUMPDEST,
   pushAt 3038 2 8224,
   opAt 3039 .MLOAD,
   opAt 3040 .ISZERO,
   pushAt 3041 2 4118,
   opAt 3042 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3043 0 0,
   pushAt 3044 2 9440,
   opAt 3045 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3046 .JUMPDEST,
   opAt 3047 (.Dup ⟨0, by decide⟩),
   opAt 3048 .MLOAD,
   pushAt 3049 2 8256,
   opAt 3050 (.Dup ⟨2, by decide⟩),
   opAt 3051 .SUB,
   opAt 3052 .MLOAD,
   opAt 3053 (.Dup ⟨1, by decide⟩),
   opAt 3054 (.Dup ⟨1, by decide⟩),
   opAt 3055 .GT,
   opAt 3056 (.Swap ⟨1, by decide⟩),
   opAt 3057 .SUB,
   opAt 3058 (.Dup ⟨3, by decide⟩),
   opAt 3059 (.Dup ⟨1, by decide⟩),
   opAt 3060 .LT,
   opAt 3061 (.Swap ⟨0, by decide⟩),
   opAt 3062 (.Dup ⟨4, by decide⟩),
   opAt 3063 (.Swap ⟨0, by decide⟩),
   opAt 3064 .SUB,
   opAt 3065 (.Dup ⟨3, by decide⟩),
   opAt 3066 .MSTORE,
   opAt 3067 .OR,
   opAt 3068 (.Swap ⟨1, by decide⟩),
   opAt 3069 .POP,
   pushAt 3070 1 31,
   opAt 3071 .NOT,
   opAt 3072 .ADD,
   pushAt 3073 2 8255,
   opAt 3074 (.Dup ⟨1, by decide⟩),
   opAt 3075 .GT,
   pushAt 3076 2 4065,
   opAt 3077 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3078 .POP,
   pushAt 3079 2 8224,
   opAt 3080 .MLOAD,
   opAt 3081 .SUB,
   pushAt 3082 2 8224,
   opAt 3083 .MSTORE,
   pushAt 3084 2 4050,
   opAt 3085 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3086 .JUMPDEST,
   pushAt 3087 2 4129,
   pushAt 3088 2 2048,
   pushAt 3089 2 3815,
   opAt 3090 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3091 .JUMPDEST,
   pushAt 3092 1 1,
   opAt 3093 (.Swap ⟨0, by decide⟩),
   opAt 3094 .SUB,
   pushAt 3095 2 3690,
   opAt 3096 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3097 .JUMPDEST,
   opAt 3098 .POP,
   pushAt 3099 2 1617,
   opAt 3100 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3496 = true :=
  Artifact.isValidJumpDest_index 2653 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3540 = true :=
  Artifact.isValidJumpDest_index 2680 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3545 = true :=
  Artifact.isValidJumpDest_index 2683 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3552 = true :=
  Artifact.isValidJumpDest_index 2687 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3583 = true :=
  Artifact.isValidJumpDest_index 2711 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2799 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3806 = true :=
  Artifact.isValidJumpDest_index 2878 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3983 = true :=
  Artifact.isValidJumpDest_index 2985 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3989 = true :=
  Artifact.isValidJumpDest_index 2989 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4050 = true :=
  Artifact.isValidJumpDest_index 3037 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4065 = true :=
  Artifact.isValidJumpDest_index 3046 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4118 = true :=
  Artifact.isValidJumpDest_index 3086 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4129 = true :=
  Artifact.isValidJumpDest_index 3091 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4138 = true :=
  Artifact.isValidJumpDest_index 3097 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
