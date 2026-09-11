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
   pushAt 2678 2 3811,
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
   pushAt 2802 2 4134,
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
   opAt 2854 .GT,
   opAt 2855 (.Dup ⟨1, by decide⟩),
   pushAt 2856 0 0,
   opAt 2857 .LT,
   opAt 2858 .AND,
   opAt 2859 (.Swap ⟨0, by decide⟩),
   opAt 2860 .SUB,
   opAt 2861 (.Swap ⟨0, by decide⟩),
   pushAt 2862 2 6176,
   opAt 2863 .MLOAD,
   opAt 2864 .GT,
   opAt 2865 .ISZERO,
   pushAt 2866 0 0,
   opAt 2867 .SUB,
   opAt 2868 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2869 0 0,
   pushAt 2870 2 9440,
   opAt 2871 .MLOAD,
   pushAt 2872 2 9408,
   opAt 2873 .MLOAD,
   pushAt 2874 2 5120,
   opAt 2875 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2876 .JUMPDEST,
   opAt 2877 (.Dup ⟨0, by decide⟩),
   opAt 2878 .MLOAD,
   pushAt 2879 0 0,
   opAt 2880 .NOT,
   pushAt 2881 2 3837,
   opAt 2882 .JUMP,
   opAt 2897 .JUMPDEST,
   opAt 2898 (.Dup ⟨5, by decide⟩),
   opAt 2899 (.Dup ⟨2, by decide⟩),
   opAt 2900 .MUL,
   opAt 2901 (.Swap ⟨1, by decide⟩),
   opAt 2902 (.Dup ⟨6, by decide⟩),
   opAt 2903 .MULMOD,
   opAt 2904 (.Dup ⟨1, by decide⟩),
   opAt 2905 (.Dup ⟨1, by decide⟩),
   opAt 2906 .LT,
   opAt 2907 .SUB,
   opAt 2908 (.Dup ⟨4, by decide⟩),
   opAt 2909 (.Dup ⟨2, by decide⟩),
   opAt 2910 .ADD,
   opAt 2911 (.Dup ⟨0, by decide⟩),
   opAt 2912 (.Swap ⟨5, by decide⟩),
   opAt 2913 .GT,
   opAt 2914 .SUB,
   opAt 2915 .SUB,
   opAt 2916 (.Dup ⟨3, by decide⟩),
   opAt 2917 (.Dup ⟨3, by decide⟩),
   opAt 2918 .MLOAD,
   opAt 2919 .ADD,
   opAt 2920 (.Dup ⟨0, by decide⟩),
   opAt 2921 (.Swap ⟨4, by decide⟩),
   opAt 2922 .GT,
   opAt 2923 .ADD,
   opAt 2924 (.Swap ⟨2, by decide⟩),
   opAt 2925 (.Dup ⟨2, by decide⟩),
   pushAt 2926 5 31,
   opAt 2927 .NOT,
   pushAt 2928 2 3898,
   opAt 2929 .JUMP,
   opAt 2944 .JUMPDEST,
   opAt 2945 .ADD,
   opAt 2946 (.Swap ⟨2, by decide⟩),
   opAt 2947 .MSTORE,
   pushAt 2948 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2949 .ADD,
   pushAt 2950 2 8224,
   opAt 2951 (.Dup ⟨2, by decide⟩),
   opAt 2952 .GT,
   pushAt 2953 2 3802,
   opAt 2954 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2955 .POP,
   opAt 2956 .POP,
   pushAt 2957 2 8224,
   opAt 2958 .MLOAD,
   opAt 2959 (.Dup ⟨1, by decide⟩),
   opAt 2960 .ADD,
   opAt 2961 (.Dup ⟨1, by decide⟩),
   opAt 2962 (.Dup ⟨1, by decide⟩),
   opAt 2963 .LT,
   opAt 2964 (.Swap ⟨1, by decide⟩),
   opAt 2965 .POP,
   opAt 2966 (.Dup ⟨2, by decide⟩),
   opAt 2967 (.Dup ⟨1, by decide⟩),
   opAt 2968 .LT,
   opAt 2969 (.Swap ⟨0, by decide⟩),
   opAt 2970 (.Dup ⟨3, by decide⟩),
   opAt 2971 (.Swap ⟨0, by decide⟩),
   opAt 2972 .SUB,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   pushAt 2974 2 8224,
   opAt 2975 .MSTORE,
   opAt 2976 .POP,
   opAt 2977 .GT,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 .POP,
   opAt 2980 .ISZERO,
   pushAt 2981 2 4046,
   opAt 2982 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2983 .JUMPDEST,
   pushAt 2984 0 0,
   pushAt 2985 2 9440,
   opAt 2986 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2987 .JUMPDEST,
   opAt 2988 (.Dup ⟨0, by decide⟩),
   opAt 2989 .MLOAD,
   opAt 2990 (.Dup ⟨1, by decide⟩),
   pushAt 2991 2 8256,
   opAt 2992 (.Swap ⟨0, by decide⟩),
   opAt 2993 .SUB,
   opAt 2994 .MLOAD,
   opAt 2995 (.Dup ⟨1, by decide⟩),
   opAt 2996 .ADD,
   opAt 2997 (.Dup ⟨0, by decide⟩),
   opAt 2998 (.Dup ⟨2, by decide⟩),
   opAt 2999 .GT,
   opAt 3000 (.Swap ⟨1, by decide⟩),
   opAt 3001 .POP,
   opAt 3002 (.Dup ⟨3, by decide⟩),
   opAt 3003 .ADD,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 (.Dup ⟨4, by decide⟩),
   opAt 3006 .GT,
   opAt 3007 (.Swap ⟨3, by decide⟩),
   opAt 3008 .POP,
   opAt 3009 (.Dup ⟨2, by decide⟩),
   opAt 3010 .MSTORE,
   opAt 3011 (.Swap ⟨0, by decide⟩),
   opAt 3012 (.Swap ⟨1, by decide⟩),
   opAt 3013 .OR,
   opAt 3014 (.Swap ⟨0, by decide⟩),
   pushAt 3015 1 31,
   opAt 3016 .NOT,
   opAt 3017 .ADD,
   pushAt 3018 2 8255,
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 .GT,
   pushAt 3021 2 3985,
   opAt 3022 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3023 .POP,
   pushAt 3024 2 8224,
   opAt 3025 .MLOAD,
   opAt 3026 (.Dup ⟨1, by decide⟩),
   opAt 3027 .ADD,
   opAt 3028 (.Dup ⟨0, by decide⟩),
   pushAt 3029 2 8224,
   opAt 3030 .MSTORE,
   opAt 3031 .LT,
   opAt 3032 .ISZERO,
   pushAt 3033 2 3979,
   opAt 3034 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3035 .JUMPDEST,
   pushAt 3036 2 8224,
   opAt 3037 .MLOAD,
   opAt 3038 .ISZERO,
   pushAt 3039 2 4114,
   opAt 3040 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3041 0 0,
   pushAt 3042 2 9440,
   opAt 3043 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3044 .JUMPDEST,
   opAt 3045 (.Dup ⟨0, by decide⟩),
   opAt 3046 .MLOAD,
   pushAt 3047 2 8256,
   opAt 3048 (.Dup ⟨2, by decide⟩),
   opAt 3049 .SUB,
   opAt 3050 .MLOAD,
   opAt 3051 (.Dup ⟨1, by decide⟩),
   opAt 3052 (.Dup ⟨1, by decide⟩),
   opAt 3053 .GT,
   opAt 3054 (.Swap ⟨1, by decide⟩),
   opAt 3055 .SUB,
   opAt 3056 (.Dup ⟨3, by decide⟩),
   opAt 3057 (.Dup ⟨1, by decide⟩),
   opAt 3058 .LT,
   opAt 3059 (.Swap ⟨0, by decide⟩),
   opAt 3060 (.Dup ⟨4, by decide⟩),
   opAt 3061 (.Swap ⟨0, by decide⟩),
   opAt 3062 .SUB,
   opAt 3063 (.Dup ⟨3, by decide⟩),
   opAt 3064 .MSTORE,
   opAt 3065 .OR,
   opAt 3066 (.Swap ⟨1, by decide⟩),
   opAt 3067 .POP,
   pushAt 3068 1 31,
   opAt 3069 .NOT,
   opAt 3070 .ADD,
   pushAt 3071 2 8255,
   opAt 3072 (.Dup ⟨1, by decide⟩),
   opAt 3073 .GT,
   pushAt 3074 2 4061,
   opAt 3075 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3076 .POP,
   pushAt 3077 2 8224,
   opAt 3078 .MLOAD,
   opAt 3079 .SUB,
   pushAt 3080 2 8224,
   opAt 3081 .MSTORE,
   pushAt 3082 2 4046,
   opAt 3083 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3084 .JUMPDEST,
   pushAt 3085 2 4125,
   pushAt 3086 2 2048,
   pushAt 3087 2 3811,
   opAt 3088 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3089 .JUMPDEST,
   pushAt 3090 1 1,
   opAt 3091 (.Swap ⟨0, by decide⟩),
   opAt 3092 .SUB,
   pushAt 3093 2 3690,
   opAt 3094 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3095 .JUMPDEST,
   opAt 3096 .POP,
   pushAt 3097 2 3324,
   opAt 3098 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3802 = true :=
  Artifact.isValidJumpDest_index 2876 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3979 = true :=
  Artifact.isValidJumpDest_index 2983 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3985 = true :=
  Artifact.isValidJumpDest_index 2987 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4046 = true :=
  Artifact.isValidJumpDest_index 3035 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4061 = true :=
  Artifact.isValidJumpDest_index 3044 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4114 = true :=
  Artifact.isValidJumpDest_index 3084 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4125 = true :=
  Artifact.isValidJumpDest_index 3089 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4134 = true :=
  Artifact.isValidJumpDest_index 3095 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
