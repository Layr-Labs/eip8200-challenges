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
  [opAt 2655 .JUMPDEST,
   opAt 2656 (.Dup ⟨0, by decide⟩),
   opAt 2657 (.Dup ⟨3, by decide⟩),
   opAt 2658 .EQ,
   pushAt 2659 0 0,
   opAt 2660 .MLOAD,
   pushAt 2661 1 255,
   opAt 2662 .SHR,
   opAt 2663 .AND,
   opAt 2664 .ISZERO,
   pushAt 2665 2 3540,
   opAt 2666 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2667 (.Dup ⟨0, by decide⟩),
   pushAt 2668 1 96,
   pushAt 2669 2 1024,
   opAt 2670 .CALLDATACOPY,
   opAt 2671 (.Dup ⟨0, by decide⟩),
   pushAt 2672 1 96,
   pushAt 2673 2 8256,
   opAt 2674 .CALLDATACOPY,
   pushAt 2675 0 0,
   pushAt 2676 2 8224,
   opAt 2677 .MSTORE,
   pushAt 2678 2 3545,
   pushAt 2679 2 2048,
   pushAt 2680 2 4902,
   opAt 2681 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2682 .JUMPDEST,
   pushAt 2683 2 1445,
   opAt 2684 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2685 .JUMPDEST,
   pushAt 2686 1 1,
   pushAt 2687 2 9408,
   opAt 2688 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2689 .JUMPDEST,
   opAt 2690 (.Dup ⟨0, by decide⟩),
   opAt 2691 .MLOAD,
   opAt 2692 .NOT,
   opAt 2693 (.Dup ⟨2, by decide⟩),
   opAt 2694 .ADD,
   opAt 2695 (.Dup ⟨2, by decide⟩),
   opAt 2696 (.Dup ⟨1, by decide⟩),
   opAt 2697 .LT,
   opAt 2698 (.Swap ⟨2, by decide⟩),
   opAt 2699 .POP,
   opAt 2700 (.Dup ⟨1, by decide⟩),
   pushAt 2701 2 5120,
   opAt 2702 .ADD,
   opAt 2703 .MSTORE,
   opAt 2704 (.Dup ⟨0, by decide⟩),
   opAt 2705 .ISZERO,
   pushAt 2706 2 3583,
   opAt 2707 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2708 1 31,
   opAt 2709 .NOT,
   opAt 2710 .ADD,
   pushAt 2711 2 3552,
   opAt 2712 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2713 .JUMPDEST,
   opAt 2714 .POP,
   opAt 2715 .POP,
   pushAt 2716 0 0,
   opAt 2717 .MLOAD,
   opAt 2718 (.Dup ⟨0, by decide⟩),
   pushAt 2719 0 0,
   opAt 2720 .SUB,
   opAt 2721 (.Dup ⟨1, by decide⟩),
   opAt 2722 .AND,
   opAt 2723 (.Dup ⟨0, by decide⟩),
   pushAt 2724 2 6144,
   opAt 2725 .MSTORE,
   opAt 2726 (.Dup ⟨0, by decide⟩),
   opAt 2727 (.Dup ⟨2, by decide⟩),
   opAt 2728 .DIV,
   opAt 2729 (.Dup ⟨0, by decide⟩),
   pushAt 2730 2 6176,
   opAt 2731 .MSTORE,
   opAt 2732 (.Dup ⟨1, by decide⟩),
   pushAt 2733 0 0,
   opAt 2734 .SUB,
   opAt 2735 (.Dup ⟨2, by decide⟩),
   opAt 2736 (.Swap ⟨0, by decide⟩),
   opAt 2737 .DIV,
   pushAt 2738 1 1,
   opAt 2739 .ADD,
   pushAt 2740 2 6208,
   opAt 2741 .MSTORE,
   opAt 2742 (.Dup ⟨0, by decide⟩),
   pushAt 2743 0 0,
   opAt 2744 .SUB,
   opAt 2745 (.Dup ⟨1, by decide⟩),
   opAt 2746 (.Swap ⟨0, by decide⟩),
   opAt 2747 .MOD,
   pushAt 2748 2 6240,
   opAt 2749 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2750 (.Dup ⟨0, by decide⟩),
   pushAt 2751 1 2,
   opAt 2752 .SUB,
   opAt 2753 (.Dup ⟨0, by decide⟩),
   opAt 2754 (.Dup ⟨2, by decide⟩),
   opAt 2755 .MUL,
   pushAt 2756 1 2,
   opAt 2757 .SUB,
   opAt 2758 .MUL,
   opAt 2759 (.Dup ⟨0, by decide⟩),
   opAt 2760 (.Dup ⟨2, by decide⟩),
   opAt 2761 .MUL,
   pushAt 2762 1 2,
   opAt 2763 .SUB,
   opAt 2764 .MUL,
   opAt 2765 (.Dup ⟨0, by decide⟩),
   opAt 2766 (.Dup ⟨2, by decide⟩),
   opAt 2767 .MUL,
   pushAt 2768 1 2,
   opAt 2769 .SUB,
   opAt 2770 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2771 (.Dup ⟨0, by decide⟩),
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
   opAt 2794 .MUL,
   pushAt 2795 2 6272,
   opAt 2796 .MSTORE,
   opAt 2797 .POP,
   opAt 2798 .POP,
   opAt 2799 .POP,
   opAt 2800 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2801 .JUMPDEST,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   opAt 2803 .ISZERO,
   pushAt 2804 2 4043,
   opAt 2805 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2806 (.Dup ⟨1, by decide⟩),
   pushAt 2807 2 2048,
   pushAt 2808 2 8224,
   opAt 2809 .MCOPY,
   pushAt 2810 0 0,
   pushAt 2811 2 9440,
   opAt 2812 .MLOAD,
   opAt 2813 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2814 2 2048,
   opAt 2815 .MLOAD,
   pushAt 2816 2 6144,
   opAt 2817 .MLOAD,
   opAt 2818 (.Dup ⟨0, by decide⟩),
   opAt 2819 (.Dup ⟨2, by decide⟩),
   opAt 2820 .DIV,
   opAt 2821 (.Swap ⟨1, by decide⟩),
   opAt 2822 .MOD,
   pushAt 2823 2 6208,
   opAt 2824 .MLOAD,
   opAt 2825 .MUL,
   pushAt 2826 2 2080,
   opAt 2827 .MLOAD,
   pushAt 2828 2 6144,
   opAt 2829 .MLOAD,
   opAt 2830 (.Swap ⟨0, by decide⟩),
   opAt 2831 .DIV,
   opAt 2832 .ADD,
   pushAt 2833 2 6176,
   opAt 2834 .MLOAD,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   pushAt 2836 2 6240,
   opAt 2837 .MLOAD,
   opAt 2838 (.Dup ⟨4, by decide⟩),
   opAt 2839 .MULMOD,
   opAt 2840 (.Dup ⟨2, by decide⟩),
   opAt 2841 .ADDMOD,
   opAt 2842 (.Swap ⟨0, by decide⟩),
   opAt 2843 .SUB,
   pushAt 2844 2 6272,
   opAt 2845 .MLOAD,
   opAt 2846 .MUL,
   opAt 2847 (.Dup ⟨0, by decide⟩),
   pushAt 2848 0 0,
   opAt 2849 .MLOAD,
   opAt 2850 .MUL,
   pushAt 2851 2 2080,
   opAt 2852 .MLOAD,
   opAt 2853 .SUB,
   pushAt 2854 1 32,
   opAt 2855 .MLOAD,
   opAt 2856 .GT,
   opAt 2857 (.Dup ⟨1, by decide⟩),
   pushAt 2858 0 0,
   opAt 2859 .LT,
   opAt 2860 .AND,
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
   pushAt 2922 2 3805,
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
   pushAt 2951 2 3955,
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
   pushAt 2991 2 3894,
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
   pushAt 3003 2 3888,
   opAt 3004 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3005 .JUMPDEST,
   pushAt 3006 2 8224,
   opAt 3007 .MLOAD,
   opAt 3008 .ISZERO,
   pushAt 3009 2 4023,
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
   pushAt 3044 2 3970,
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
   pushAt 3052 2 3955,
   opAt 3053 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3054 .JUMPDEST,
   pushAt 3055 2 4034,
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
   pushAt 3067 2 1617,
   opAt 3068 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3496 = true :=
  Artifact.isValidJumpDest_index 2655 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3540 = true :=
  Artifact.isValidJumpDest_index 2682 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3545 = true :=
  Artifact.isValidJumpDest_index 2685 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3552 = true :=
  Artifact.isValidJumpDest_index 2689 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3583 = true :=
  Artifact.isValidJumpDest_index 2713 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2801 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3805 = true :=
  Artifact.isValidJumpDest_index 2880 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3888 = true :=
  Artifact.isValidJumpDest_index 2953 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3894 = true :=
  Artifact.isValidJumpDest_index 2957 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3955 = true :=
  Artifact.isValidJumpDest_index 3005 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 3014 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4023 = true :=
  Artifact.isValidJumpDest_index 3054 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4034 = true :=
  Artifact.isValidJumpDest_index 3059 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4043 = true :=
  Artifact.isValidJumpDest_index 3065 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
