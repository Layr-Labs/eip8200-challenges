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
  [opAt 2657 .JUMPDEST,
   opAt 2658 (.Dup ⟨0, by decide⟩),
   opAt 2659 (.Dup ⟨3, by decide⟩),
   opAt 2660 .EQ,
   pushAt 2661 0 0,
   opAt 2662 .MLOAD,
   pushAt 2663 1 255,
   opAt 2664 .SHR,
   opAt 2665 .AND,
   opAt 2666 .ISZERO,
   pushAt 2667 2 3540,
   opAt 2668 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2669 (.Dup ⟨0, by decide⟩),
   pushAt 2670 1 96,
   pushAt 2671 2 1024,
   opAt 2672 .CALLDATACOPY,
   opAt 2673 (.Dup ⟨0, by decide⟩),
   pushAt 2674 1 96,
   pushAt 2675 2 8256,
   opAt 2676 .CALLDATACOPY,
   pushAt 2677 0 0,
   pushAt 2678 2 8224,
   opAt 2679 .MSTORE,
   pushAt 2680 2 3545,
   pushAt 2681 2 2048,
   pushAt 2682 2 4902,
   opAt 2683 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2684 .JUMPDEST,
   pushAt 2685 2 1445,
   opAt 2686 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2687 .JUMPDEST,
   pushAt 2688 1 1,
   pushAt 2689 2 9408,
   opAt 2690 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2691 .JUMPDEST,
   opAt 2692 (.Dup ⟨0, by decide⟩),
   opAt 2693 .MLOAD,
   opAt 2694 .NOT,
   opAt 2695 (.Dup ⟨2, by decide⟩),
   opAt 2696 .ADD,
   opAt 2697 (.Dup ⟨2, by decide⟩),
   opAt 2698 (.Dup ⟨1, by decide⟩),
   opAt 2699 .LT,
   opAt 2700 (.Swap ⟨2, by decide⟩),
   opAt 2701 .POP,
   opAt 2702 (.Dup ⟨1, by decide⟩),
   pushAt 2703 2 5120,
   opAt 2704 .ADD,
   opAt 2705 .MSTORE,
   opAt 2706 (.Dup ⟨0, by decide⟩),
   opAt 2707 .ISZERO,
   pushAt 2708 2 3583,
   opAt 2709 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2710 1 31,
   opAt 2711 .NOT,
   opAt 2712 .ADD,
   pushAt 2713 2 3552,
   opAt 2714 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2715 .JUMPDEST,
   opAt 2716 .POP,
   opAt 2717 .POP,
   pushAt 2718 0 0,
   opAt 2719 .MLOAD,
   opAt 2720 (.Dup ⟨0, by decide⟩),
   pushAt 2721 0 0,
   opAt 2722 .SUB,
   opAt 2723 (.Dup ⟨1, by decide⟩),
   opAt 2724 .AND,
   opAt 2725 (.Dup ⟨0, by decide⟩),
   pushAt 2726 2 6144,
   opAt 2727 .MSTORE,
   opAt 2728 (.Dup ⟨0, by decide⟩),
   opAt 2729 (.Dup ⟨2, by decide⟩),
   opAt 2730 .DIV,
   opAt 2731 (.Dup ⟨0, by decide⟩),
   pushAt 2732 2 6176,
   opAt 2733 .MSTORE,
   opAt 2734 (.Dup ⟨1, by decide⟩),
   pushAt 2735 0 0,
   opAt 2736 .SUB,
   opAt 2737 (.Dup ⟨2, by decide⟩),
   opAt 2738 (.Swap ⟨0, by decide⟩),
   opAt 2739 .DIV,
   pushAt 2740 1 1,
   opAt 2741 .ADD,
   pushAt 2742 2 6208,
   opAt 2743 .MSTORE,
   opAt 2744 (.Dup ⟨0, by decide⟩),
   pushAt 2745 0 0,
   opAt 2746 .SUB,
   opAt 2747 (.Dup ⟨1, by decide⟩),
   opAt 2748 (.Swap ⟨0, by decide⟩),
   opAt 2749 .MOD,
   pushAt 2750 2 6240,
   opAt 2751 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2752 (.Dup ⟨0, by decide⟩),
   pushAt 2753 1 2,
   opAt 2754 .SUB,
   opAt 2755 (.Dup ⟨0, by decide⟩),
   opAt 2756 (.Dup ⟨2, by decide⟩),
   opAt 2757 .MUL,
   pushAt 2758 1 2,
   opAt 2759 .SUB,
   opAt 2760 .MUL,
   opAt 2761 (.Dup ⟨0, by decide⟩),
   opAt 2762 (.Dup ⟨2, by decide⟩),
   opAt 2763 .MUL,
   pushAt 2764 1 2,
   opAt 2765 .SUB,
   opAt 2766 .MUL,
   opAt 2767 (.Dup ⟨0, by decide⟩),
   opAt 2768 (.Dup ⟨2, by decide⟩),
   opAt 2769 .MUL,
   pushAt 2770 1 2,
   opAt 2771 .SUB,
   opAt 2772 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2773 (.Dup ⟨0, by decide⟩),
   opAt 2774 (.Dup ⟨2, by decide⟩),
   opAt 2775 .MUL,
   pushAt 2776 1 2,
   opAt 2777 .SUB,
   opAt 2778 .MUL,
   opAt 2779 (.Dup ⟨0, by decide⟩),
   opAt 2780 (.Dup ⟨2, by decide⟩),
   opAt 2781 .MUL,
   pushAt 2782 1 2,
   opAt 2783 .SUB,
   opAt 2784 .MUL,
   opAt 2785 (.Dup ⟨0, by decide⟩),
   opAt 2786 (.Dup ⟨2, by decide⟩),
   opAt 2787 .MUL,
   pushAt 2788 1 2,
   opAt 2789 .SUB,
   opAt 2790 .MUL,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   opAt 2792 (.Dup ⟨2, by decide⟩),
   opAt 2793 .MUL,
   pushAt 2794 1 2,
   opAt 2795 .SUB,
   opAt 2796 .MUL,
   pushAt 2797 2 6272,
   opAt 2798 .MSTORE,
   opAt 2799 .POP,
   opAt 2800 .POP,
   opAt 2801 .POP,
   opAt 2802 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2803 .JUMPDEST,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   opAt 2805 .ISZERO,
   pushAt 2806 2 4043,
   opAt 2807 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2808 (.Dup ⟨1, by decide⟩),
   pushAt 2809 2 2048,
   pushAt 2810 2 8224,
   opAt 2811 .MCOPY,
   pushAt 2812 0 0,
   pushAt 2813 2 9440,
   opAt 2814 .MLOAD,
   opAt 2815 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2816 2 2048,
   opAt 2817 .MLOAD,
   pushAt 2818 2 6144,
   opAt 2819 .MLOAD,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   opAt 2821 (.Dup ⟨2, by decide⟩),
   opAt 2822 .DIV,
   opAt 2823 (.Swap ⟨1, by decide⟩),
   opAt 2824 .MOD,
   pushAt 2825 2 6208,
   opAt 2826 .MLOAD,
   opAt 2827 .MUL,
   pushAt 2828 2 2080,
   opAt 2829 .MLOAD,
   pushAt 2830 2 6144,
   opAt 2831 .MLOAD,
   opAt 2832 (.Swap ⟨0, by decide⟩),
   opAt 2833 .DIV,
   opAt 2834 .ADD,
   pushAt 2835 2 6176,
   opAt 2836 .MLOAD,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   pushAt 2838 2 6240,
   opAt 2839 .MLOAD,
   opAt 2840 (.Dup ⟨4, by decide⟩),
   opAt 2841 .MULMOD,
   opAt 2842 (.Dup ⟨2, by decide⟩),
   opAt 2843 .ADDMOD,
   opAt 2844 (.Swap ⟨0, by decide⟩),
   opAt 2845 .SUB,
   pushAt 2846 2 6272,
   opAt 2847 .MLOAD,
   opAt 2848 .MUL,
   opAt 2849 (.Dup ⟨0, by decide⟩),
   pushAt 2850 0 0,
   opAt 2851 .MLOAD,
   opAt 2852 .MUL,
   pushAt 2853 2 2080,
   opAt 2854 .MLOAD,
   opAt 2855 .SUB,
   pushAt 2856 1 32,
   opAt 2857 .MLOAD,
   opAt 2858 .GT,
   opAt 2859 (.Dup ⟨1, by decide⟩),
   pushAt 2860 0 0,
   opAt 2861 .LT,
   opAt 2862 .AND,
   opAt 2863 (.Swap ⟨0, by decide⟩),
   opAt 2864 .SUB,
   opAt 2865 (.Swap ⟨0, by decide⟩),
   pushAt 2866 2 6176,
   opAt 2867 .MLOAD,
   opAt 2868 .GT,
   opAt 2869 .ISZERO,
   pushAt 2870 0 0,
   opAt 2871 .SUB,
   opAt 2872 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2873 0 0,
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
   opAt 2885 (.Dup ⟨5, by decide⟩),
   opAt 2886 (.Dup ⟨2, by decide⟩),
   opAt 2887 .MUL,
   opAt 2888 (.Swap ⟨1, by decide⟩),
   opAt 2889 (.Dup ⟨6, by decide⟩),
   opAt 2890 .MULMOD,
   opAt 2891 (.Dup ⟨1, by decide⟩),
   opAt 2892 (.Dup ⟨1, by decide⟩),
   opAt 2893 .LT,
   opAt 2894 .SUB,
   opAt 2895 (.Dup ⟨4, by decide⟩),
   opAt 2896 (.Dup ⟨2, by decide⟩),
   opAt 2897 .ADD,
   opAt 2898 (.Dup ⟨0, by decide⟩),
   opAt 2899 (.Swap ⟨5, by decide⟩),
   opAt 2900 .GT,
   opAt 2901 .SUB,
   opAt 2902 .SUB,
   opAt 2903 (.Dup ⟨3, by decide⟩),
   opAt 2904 (.Dup ⟨3, by decide⟩),
   opAt 2905 .MLOAD,
   opAt 2906 .ADD,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 (.Swap ⟨4, by decide⟩),
   opAt 2909 .GT,
   opAt 2910 .ADD,
   opAt 2911 (.Swap ⟨2, by decide⟩),
   opAt 2912 (.Dup ⟨2, by decide⟩),
   pushAt 2913 1 31,
   opAt 2914 .NOT,
   opAt 2915 .ADD,
   opAt 2916 (.Swap ⟨2, by decide⟩),
   opAt 2917 .MSTORE,
   pushAt 2918 1 31,
   opAt 2919 .NOT,
   opAt 2920 .ADD,
   pushAt 2921 2 8224,
   opAt 2922 (.Dup ⟨2, by decide⟩),
   opAt 2923 .GT,
   pushAt 2924 2 3802,
   opAt 2925 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2926 .POP,
   opAt 2927 .POP,
   pushAt 2928 2 8224,
   opAt 2929 .MLOAD,
   opAt 2930 (.Dup ⟨1, by decide⟩),
   opAt 2931 .ADD,
   opAt 2932 (.Dup ⟨1, by decide⟩),
   opAt 2933 (.Dup ⟨1, by decide⟩),
   opAt 2934 .LT,
   opAt 2935 (.Swap ⟨1, by decide⟩),
   opAt 2936 .POP,
   opAt 2937 (.Dup ⟨2, by decide⟩),
   opAt 2938 (.Dup ⟨1, by decide⟩),
   opAt 2939 .LT,
   opAt 2940 (.Swap ⟨0, by decide⟩),
   opAt 2941 (.Dup ⟨3, by decide⟩),
   opAt 2942 (.Swap ⟨0, by decide⟩),
   opAt 2943 .SUB,
   opAt 2944 (.Dup ⟨0, by decide⟩),
   pushAt 2945 2 8224,
   opAt 2946 .MSTORE,
   opAt 2947 .POP,
   opAt 2948 .GT,
   opAt 2949 (.Swap ⟨0, by decide⟩),
   opAt 2950 .POP,
   opAt 2951 .ISZERO,
   pushAt 2952 2 3955,
   opAt 2953 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2954 .JUMPDEST,
   pushAt 2955 0 0,
   pushAt 2956 2 9440,
   opAt 2957 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2958 .JUMPDEST,
   opAt 2959 (.Dup ⟨0, by decide⟩),
   opAt 2960 .MLOAD,
   opAt 2961 (.Dup ⟨1, by decide⟩),
   pushAt 2962 2 8256,
   opAt 2963 (.Swap ⟨0, by decide⟩),
   opAt 2964 .SUB,
   opAt 2965 .MLOAD,
   opAt 2966 (.Dup ⟨1, by decide⟩),
   opAt 2967 .ADD,
   opAt 2968 (.Dup ⟨0, by decide⟩),
   opAt 2969 (.Dup ⟨2, by decide⟩),
   opAt 2970 .GT,
   opAt 2971 (.Swap ⟨1, by decide⟩),
   opAt 2972 .POP,
   opAt 2973 (.Dup ⟨3, by decide⟩),
   opAt 2974 .ADD,
   opAt 2975 (.Dup ⟨0, by decide⟩),
   opAt 2976 (.Dup ⟨4, by decide⟩),
   opAt 2977 .GT,
   opAt 2978 (.Swap ⟨3, by decide⟩),
   opAt 2979 .POP,
   opAt 2980 (.Dup ⟨2, by decide⟩),
   opAt 2981 .MSTORE,
   opAt 2982 (.Swap ⟨0, by decide⟩),
   opAt 2983 (.Swap ⟨1, by decide⟩),
   opAt 2984 .OR,
   opAt 2985 (.Swap ⟨0, by decide⟩),
   pushAt 2986 1 31,
   opAt 2987 .NOT,
   opAt 2988 .ADD,
   pushAt 2989 2 8255,
   opAt 2990 (.Dup ⟨1, by decide⟩),
   opAt 2991 .GT,
   pushAt 2992 2 3894,
   opAt 2993 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2994 .POP,
   pushAt 2995 2 8224,
   opAt 2996 .MLOAD,
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 .ADD,
   opAt 2999 (.Dup ⟨0, by decide⟩),
   pushAt 3000 2 8224,
   opAt 3001 .MSTORE,
   opAt 3002 .LT,
   opAt 3003 .ISZERO,
   pushAt 3004 2 3888,
   opAt 3005 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3006 .JUMPDEST,
   pushAt 3007 2 8224,
   opAt 3008 .MLOAD,
   opAt 3009 .ISZERO,
   pushAt 3010 2 4023,
   opAt 3011 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3012 0 0,
   pushAt 3013 2 9440,
   opAt 3014 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3015 .JUMPDEST,
   opAt 3016 (.Dup ⟨0, by decide⟩),
   opAt 3017 .MLOAD,
   pushAt 3018 2 8256,
   opAt 3019 (.Dup ⟨2, by decide⟩),
   opAt 3020 .SUB,
   opAt 3021 .MLOAD,
   opAt 3022 (.Dup ⟨1, by decide⟩),
   opAt 3023 (.Dup ⟨1, by decide⟩),
   opAt 3024 .GT,
   opAt 3025 (.Swap ⟨1, by decide⟩),
   opAt 3026 .SUB,
   opAt 3027 (.Dup ⟨3, by decide⟩),
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 .LT,
   opAt 3030 (.Swap ⟨0, by decide⟩),
   opAt 3031 (.Dup ⟨4, by decide⟩),
   opAt 3032 (.Swap ⟨0, by decide⟩),
   opAt 3033 .SUB,
   opAt 3034 (.Dup ⟨3, by decide⟩),
   opAt 3035 .MSTORE,
   opAt 3036 .OR,
   opAt 3037 (.Swap ⟨1, by decide⟩),
   opAt 3038 .POP,
   pushAt 3039 1 31,
   opAt 3040 .NOT,
   opAt 3041 .ADD,
   pushAt 3042 2 8255,
   opAt 3043 (.Dup ⟨1, by decide⟩),
   opAt 3044 .GT,
   pushAt 3045 2 3970,
   opAt 3046 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3047 .POP,
   pushAt 3048 2 8224,
   opAt 3049 .MLOAD,
   opAt 3050 .SUB,
   pushAt 3051 2 8224,
   opAt 3052 .MSTORE,
   pushAt 3053 2 3955,
   opAt 3054 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3055 .JUMPDEST,
   pushAt 3056 2 4034,
   pushAt 3057 2 2048,
   pushAt 3058 2 4902,
   opAt 3059 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3060 .JUMPDEST,
   pushAt 3061 1 1,
   opAt 3062 (.Swap ⟨0, by decide⟩),
   opAt 3063 .SUB,
   pushAt 3064 2 3690,
   opAt 3065 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3066 .JUMPDEST,
   opAt 3067 .POP,
   pushAt 3068 2 1617,
   opAt 3069 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3496 = true :=
  Artifact.isValidJumpDest_index 2657 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3540 = true :=
  Artifact.isValidJumpDest_index 2684 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3545 = true :=
  Artifact.isValidJumpDest_index 2687 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3552 = true :=
  Artifact.isValidJumpDest_index 2691 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3583 = true :=
  Artifact.isValidJumpDest_index 2715 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2803 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3802 = true :=
  Artifact.isValidJumpDest_index 2880 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3888 = true :=
  Artifact.isValidJumpDest_index 2954 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3894 = true :=
  Artifact.isValidJumpDest_index 2958 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3955 = true :=
  Artifact.isValidJumpDest_index 3006 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 3015 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4023 = true :=
  Artifact.isValidJumpDest_index 3055 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4034 = true :=
  Artifact.isValidJumpDest_index 3060 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4043 = true :=
  Artifact.isValidJumpDest_index 3066 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
