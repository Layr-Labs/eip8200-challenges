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
   pushAt 2802 2 4043,
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
   opAt 2881 (.Dup ⟨5, by decide⟩),
   opAt 2882 (.Dup ⟨2, by decide⟩),
   opAt 2883 .MUL,
   opAt 2884 (.Swap ⟨1, by decide⟩),
   opAt 2885 (.Dup ⟨6, by decide⟩),
   opAt 2886 .MULMOD,
   opAt 2887 (.Dup ⟨1, by decide⟩),
   opAt 2888 (.Dup ⟨1, by decide⟩),
   opAt 2889 .LT,
   opAt 2890 .SUB,
   opAt 2891 (.Dup ⟨4, by decide⟩),
   opAt 2892 (.Dup ⟨2, by decide⟩),
   opAt 2893 .ADD,
   opAt 2894 (.Dup ⟨0, by decide⟩),
   opAt 2895 (.Swap ⟨5, by decide⟩),
   opAt 2896 .GT,
   opAt 2897 .SUB,
   opAt 2898 .SUB,
   opAt 2899 (.Dup ⟨3, by decide⟩),
   opAt 2900 (.Dup ⟨3, by decide⟩),
   opAt 2901 .MLOAD,
   opAt 2902 .ADD,
   opAt 2903 (.Dup ⟨0, by decide⟩),
   opAt 2904 (.Swap ⟨4, by decide⟩),
   opAt 2905 .GT,
   opAt 2906 .ADD,
   opAt 2907 (.Swap ⟨2, by decide⟩),
   opAt 2908 (.Dup ⟨2, by decide⟩),
   pushAt 2909 1 31,
   opAt 2910 .NOT,
   opAt 2911 .ADD,
   opAt 2912 (.Swap ⟨2, by decide⟩),
   opAt 2913 .MSTORE,
   pushAt 2914 1 31,
   opAt 2915 .NOT,
   opAt 2916 .ADD,
   pushAt 2917 2 8224,
   opAt 2918 (.Dup ⟨2, by decide⟩),
   opAt 2919 .GT,
   pushAt 2920 2 3802,
   opAt 2921 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2922 .POP,
   opAt 2923 .POP,
   pushAt 2924 2 8224,
   opAt 2925 .MLOAD,
   opAt 2926 (.Dup ⟨1, by decide⟩),
   opAt 2927 .ADD,
   opAt 2928 (.Dup ⟨1, by decide⟩),
   opAt 2929 (.Dup ⟨1, by decide⟩),
   opAt 2930 .LT,
   opAt 2931 (.Swap ⟨1, by decide⟩),
   opAt 2932 .POP,
   opAt 2933 (.Dup ⟨2, by decide⟩),
   opAt 2934 (.Dup ⟨1, by decide⟩),
   opAt 2935 .LT,
   opAt 2936 (.Swap ⟨0, by decide⟩),
   opAt 2937 (.Dup ⟨3, by decide⟩),
   opAt 2938 (.Swap ⟨0, by decide⟩),
   opAt 2939 .SUB,
   opAt 2940 (.Dup ⟨0, by decide⟩),
   pushAt 2941 2 8224,
   opAt 2942 .MSTORE,
   opAt 2943 .POP,
   opAt 2944 .GT,
   opAt 2945 (.Swap ⟨0, by decide⟩),
   opAt 2946 .POP,
   opAt 2947 .ISZERO,
   pushAt 2948 2 3955,
   opAt 2949 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2950 .JUMPDEST,
   pushAt 2951 0 0,
   pushAt 2952 2 9440,
   opAt 2953 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2954 .JUMPDEST,
   opAt 2955 (.Dup ⟨0, by decide⟩),
   opAt 2956 .MLOAD,
   opAt 2957 (.Dup ⟨1, by decide⟩),
   pushAt 2958 2 8256,
   opAt 2959 (.Swap ⟨0, by decide⟩),
   opAt 2960 .SUB,
   opAt 2961 .MLOAD,
   opAt 2962 (.Dup ⟨1, by decide⟩),
   opAt 2963 .ADD,
   opAt 2964 (.Dup ⟨0, by decide⟩),
   opAt 2965 (.Dup ⟨2, by decide⟩),
   opAt 2966 .GT,
   opAt 2967 (.Swap ⟨1, by decide⟩),
   opAt 2968 .POP,
   opAt 2969 (.Dup ⟨3, by decide⟩),
   opAt 2970 .ADD,
   opAt 2971 (.Dup ⟨0, by decide⟩),
   opAt 2972 (.Dup ⟨4, by decide⟩),
   opAt 2973 .GT,
   opAt 2974 (.Swap ⟨3, by decide⟩),
   opAt 2975 .POP,
   opAt 2976 (.Dup ⟨2, by decide⟩),
   opAt 2977 .MSTORE,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 (.Swap ⟨1, by decide⟩),
   opAt 2980 .OR,
   opAt 2981 (.Swap ⟨0, by decide⟩),
   pushAt 2982 1 31,
   opAt 2983 .NOT,
   opAt 2984 .ADD,
   pushAt 2985 2 8255,
   opAt 2986 (.Dup ⟨1, by decide⟩),
   opAt 2987 .GT,
   pushAt 2988 2 3894,
   opAt 2989 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2990 .POP,
   pushAt 2991 2 8224,
   opAt 2992 .MLOAD,
   opAt 2993 (.Dup ⟨1, by decide⟩),
   opAt 2994 .ADD,
   opAt 2995 (.Dup ⟨0, by decide⟩),
   pushAt 2996 2 8224,
   opAt 2997 .MSTORE,
   opAt 2998 .LT,
   opAt 2999 .ISZERO,
   pushAt 3000 2 3888,
   opAt 3001 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3002 .JUMPDEST,
   pushAt 3003 2 8224,
   opAt 3004 .MLOAD,
   opAt 3005 .ISZERO,
   pushAt 3006 2 4023,
   opAt 3007 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3008 0 0,
   pushAt 3009 2 9440,
   opAt 3010 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3011 .JUMPDEST,
   opAt 3012 (.Dup ⟨0, by decide⟩),
   opAt 3013 .MLOAD,
   pushAt 3014 2 8256,
   opAt 3015 (.Dup ⟨2, by decide⟩),
   opAt 3016 .SUB,
   opAt 3017 .MLOAD,
   opAt 3018 (.Dup ⟨1, by decide⟩),
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 .GT,
   opAt 3021 (.Swap ⟨1, by decide⟩),
   opAt 3022 .SUB,
   opAt 3023 (.Dup ⟨3, by decide⟩),
   opAt 3024 (.Dup ⟨1, by decide⟩),
   opAt 3025 .LT,
   opAt 3026 (.Swap ⟨0, by decide⟩),
   opAt 3027 (.Dup ⟨4, by decide⟩),
   opAt 3028 (.Swap ⟨0, by decide⟩),
   opAt 3029 .SUB,
   opAt 3030 (.Dup ⟨3, by decide⟩),
   opAt 3031 .MSTORE,
   opAt 3032 .OR,
   opAt 3033 (.Swap ⟨1, by decide⟩),
   opAt 3034 .POP,
   pushAt 3035 1 31,
   opAt 3036 .NOT,
   opAt 3037 .ADD,
   pushAt 3038 2 8255,
   opAt 3039 (.Dup ⟨1, by decide⟩),
   opAt 3040 .GT,
   pushAt 3041 2 3970,
   opAt 3042 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3043 .POP,
   pushAt 3044 2 8224,
   opAt 3045 .MLOAD,
   opAt 3046 .SUB,
   pushAt 3047 2 8224,
   opAt 3048 .MSTORE,
   pushAt 3049 2 3955,
   opAt 3050 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3051 .JUMPDEST,
   pushAt 3052 2 4034,
   pushAt 3053 2 2048,
   pushAt 3054 2 4902,
   opAt 3055 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3056 .JUMPDEST,
   pushAt 3057 1 1,
   opAt 3058 (.Swap ⟨0, by decide⟩),
   opAt 3059 .SUB,
   pushAt 3060 2 3690,
   opAt 3061 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3062 .JUMPDEST,
   opAt 3063 .POP,
   pushAt 3064 2 1617,
   opAt 3065 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3888 = true :=
  Artifact.isValidJumpDest_index 2950 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3894 = true :=
  Artifact.isValidJumpDest_index 2954 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3955 = true :=
  Artifact.isValidJumpDest_index 3002 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 3011 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4023 = true :=
  Artifact.isValidJumpDest_index 3051 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4034 = true :=
  Artifact.isValidJumpDest_index 3056 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4043 = true :=
  Artifact.isValidJumpDest_index 3062 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
