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
   pushAt 2678 2 4902,
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
   pushAt 2802 2 4047,
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
   pushAt 2872 1 31,
   opAt 2873 .NOT,
   pushAt 2874 2 9440,
   opAt 2875 .MLOAD,
   pushAt 2876 2 9408,
   opAt 2877 .MLOAD,
   pushAt 2878 2 5120,
   opAt 2879 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2880 .JUMPDEST,
   opAt 2881 (.Dup ⟨0, by decide⟩),
   opAt 2882 .MLOAD,
   pushAt 2883 0 0,
   opAt 2884 .NOT,
   opAt 2885 (.Dup ⟨6, by decide⟩),
   opAt 2886 (.Dup ⟨2, by decide⟩),
   opAt 2887 .MUL,
   opAt 2888 (.Swap ⟨1, by decide⟩),
   opAt 2889 (.Dup ⟨7, by decide⟩),
   opAt 2890 .MULMOD,
   opAt 2891 (.Dup ⟨1, by decide⟩),
   opAt 2892 (.Dup ⟨1, by decide⟩),
   opAt 2893 .LT,
   opAt 2894 .SUB,
   opAt 2895 (.Dup ⟨5, by decide⟩),
   opAt 2896 (.Dup ⟨2, by decide⟩),
   opAt 2897 .ADD,
   opAt 2898 (.Dup ⟨0, by decide⟩),
   opAt 2899 (.Swap ⟨6, by decide⟩),
   opAt 2900 .GT,
   opAt 2901 .SUB,
   opAt 2902 .SUB,
   opAt 2903 (.Dup ⟨4, by decide⟩),
   opAt 2904 (.Dup ⟨3, by decide⟩),
   opAt 2905 .MLOAD,
   opAt 2906 .ADD,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 (.Swap ⟨5, by decide⟩),
   opAt 2909 .GT,
   opAt 2910 .ADD,
   opAt 2911 (.Swap ⟨3, by decide⟩),
   opAt 2912 (.Dup ⟨2, by decide⟩),
   opAt 2913 (.Dup ⟨4, by decide⟩),
   opAt 2914 .ADD,
   opAt 2915 (.Swap ⟨2, by decide⟩),
   opAt 2916 .MSTORE,
   opAt 2917 (.Dup ⟨2, by decide⟩),
   opAt 2918 .ADD,
   pushAt 2919 2 8224,
   opAt 2920 (.Dup ⟨2, by decide⟩),
   opAt 2921 .GT,
   pushAt 2922 2 3809,
   opAt 2923 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2924 .POP,
   opAt 2925 .POP,
   opAt 2926 .POP,
   pushAt 2927 2 8224,
   opAt 2928 .MLOAD,
   opAt 2929 (.Dup ⟨1, by decide⟩),
   opAt 2930 .ADD,
   opAt 2931 (.Dup ⟨1, by decide⟩),
   opAt 2932 (.Dup ⟨1, by decide⟩),
   opAt 2933 .LT,
   opAt 2934 (.Swap ⟨1, by decide⟩),
   opAt 2935 .POP,
   opAt 2936 (.Dup ⟨2, by decide⟩),
   opAt 2937 (.Dup ⟨1, by decide⟩),
   opAt 2938 .LT,
   opAt 2939 (.Swap ⟨0, by decide⟩),
   opAt 2940 (.Dup ⟨3, by decide⟩),
   opAt 2941 (.Swap ⟨0, by decide⟩),
   opAt 2942 .SUB,
   opAt 2943 (.Dup ⟨0, by decide⟩),
   pushAt 2944 2 8224,
   opAt 2945 .MSTORE,
   opAt 2946 .POP,
   opAt 2947 .GT,
   opAt 2948 (.Swap ⟨0, by decide⟩),
   opAt 2949 .POP,
   opAt 2950 .ISZERO,
   pushAt 2951 2 3959,
   opAt 2952 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2953 .JUMPDEST,
   pushAt 2954 0 0,
   pushAt 2955 2 9440,
   opAt 2956 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2957 .JUMPDEST,
   opAt 2958 (.Dup ⟨0, by decide⟩),
   opAt 2959 .MLOAD,
   opAt 2960 (.Dup ⟨1, by decide⟩),
   pushAt 2961 2 8256,
   opAt 2962 (.Swap ⟨0, by decide⟩),
   opAt 2963 .SUB,
   opAt 2964 .MLOAD,
   opAt 2965 (.Dup ⟨1, by decide⟩),
   opAt 2966 .ADD,
   opAt 2967 (.Dup ⟨0, by decide⟩),
   opAt 2968 (.Dup ⟨2, by decide⟩),
   opAt 2969 .GT,
   opAt 2970 (.Swap ⟨1, by decide⟩),
   opAt 2971 .POP,
   opAt 2972 (.Dup ⟨3, by decide⟩),
   opAt 2973 .ADD,
   opAt 2974 (.Dup ⟨0, by decide⟩),
   opAt 2975 (.Dup ⟨4, by decide⟩),
   opAt 2976 .GT,
   opAt 2977 (.Swap ⟨3, by decide⟩),
   opAt 2978 .POP,
   opAt 2979 (.Dup ⟨2, by decide⟩),
   opAt 2980 .MSTORE,
   opAt 2981 (.Swap ⟨0, by decide⟩),
   opAt 2982 (.Swap ⟨1, by decide⟩),
   opAt 2983 .OR,
   opAt 2984 (.Swap ⟨0, by decide⟩),
   pushAt 2985 1 31,
   opAt 2986 .NOT,
   opAt 2987 .ADD,
   pushAt 2988 2 8255,
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 .GT,
   pushAt 2991 2 3898,
   opAt 2992 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2993 .POP,
   pushAt 2994 2 8224,
   opAt 2995 .MLOAD,
   opAt 2996 (.Dup ⟨1, by decide⟩),
   opAt 2997 .ADD,
   opAt 2998 (.Dup ⟨0, by decide⟩),
   pushAt 2999 2 8224,
   opAt 3000 .MSTORE,
   opAt 3001 .LT,
   opAt 3002 .ISZERO,
   pushAt 3003 2 3892,
   opAt 3004 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3005 .JUMPDEST,
   pushAt 3006 2 8224,
   opAt 3007 .MLOAD,
   opAt 3008 .ISZERO,
   pushAt 3009 2 4027,
   opAt 3010 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3011 0 0,
   pushAt 3012 2 9440,
   opAt 3013 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3014 .JUMPDEST,
   opAt 3015 (.Dup ⟨0, by decide⟩),
   opAt 3016 .MLOAD,
   pushAt 3017 2 8256,
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .SUB,
   opAt 3020 .MLOAD,
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 (.Dup ⟨1, by decide⟩),
   opAt 3023 .GT,
   opAt 3024 (.Swap ⟨1, by decide⟩),
   opAt 3025 .SUB,
   opAt 3026 (.Dup ⟨3, by decide⟩),
   opAt 3027 (.Dup ⟨1, by decide⟩),
   opAt 3028 .LT,
   opAt 3029 (.Swap ⟨0, by decide⟩),
   opAt 3030 (.Dup ⟨4, by decide⟩),
   opAt 3031 (.Swap ⟨0, by decide⟩),
   opAt 3032 .SUB,
   opAt 3033 (.Dup ⟨3, by decide⟩),
   opAt 3034 .MSTORE,
   opAt 3035 .OR,
   opAt 3036 (.Swap ⟨1, by decide⟩),
   opAt 3037 .POP,
   pushAt 3038 1 31,
   opAt 3039 .NOT,
   opAt 3040 .ADD,
   pushAt 3041 2 8255,
   opAt 3042 (.Dup ⟨1, by decide⟩),
   opAt 3043 .GT,
   pushAt 3044 2 3974,
   opAt 3045 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3046 .POP,
   pushAt 3047 2 8224,
   opAt 3048 .MLOAD,
   opAt 3049 .SUB,
   pushAt 3050 2 8224,
   opAt 3051 .MSTORE,
   pushAt 3052 2 3959,
   opAt 3053 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3054 .JUMPDEST,
   pushAt 3055 2 4038,
   pushAt 3056 2 2048,
   pushAt 3057 2 4902,
   opAt 3058 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3059 .JUMPDEST,
   pushAt 3060 1 1,
   opAt 3061 (.Swap ⟨0, by decide⟩),
   opAt 3062 .SUB,
   pushAt 3063 2 3690,
   opAt 3064 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3065 .JUMPDEST,
   opAt 3066 .POP,
   pushAt 3067 2 3324,
   opAt 3068 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3809 = true :=
  Artifact.isValidJumpDest_index 2880 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3892 = true :=
  Artifact.isValidJumpDest_index 2953 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3898 = true :=
  Artifact.isValidJumpDest_index 2957 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3959 = true :=
  Artifact.isValidJumpDest_index 3005 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3974 = true :=
  Artifact.isValidJumpDest_index 3014 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4027 = true :=
  Artifact.isValidJumpDest_index 3054 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4038 = true :=
  Artifact.isValidJumpDest_index 3059 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4047 = true :=
  Artifact.isValidJumpDest_index 3065 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
