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
   pushAt 2669 2 256,
   opAt 2670 .CALLDATACOPY,
   opAt 2671 (.Dup ⟨0, by decide⟩),
   pushAt 2672 1 96,
   pushAt 2673 2 2112,
   opAt 2674 .CALLDATACOPY,
   pushAt 2675 0 0,
   pushAt 2676 2 2080,
   opAt 2677 .MSTORE,
   pushAt 2678 2 3545,
   pushAt 2679 2 512,
   pushAt 2680 2 4898,
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
   pushAt 2687 2 2848,
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
   pushAt 2701 2 1280,
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
   pushAt 2724 2 1536,
   opAt 2725 .MSTORE,
   opAt 2726 (.Dup ⟨0, by decide⟩),
   opAt 2727 (.Dup ⟨2, by decide⟩),
   opAt 2728 .DIV,
   opAt 2729 (.Dup ⟨0, by decide⟩),
   pushAt 2730 2 1568,
   opAt 2731 .MSTORE,
   opAt 2732 (.Dup ⟨1, by decide⟩),
   pushAt 2733 0 0,
   opAt 2734 .SUB,
   opAt 2735 (.Dup ⟨2, by decide⟩),
   opAt 2736 (.Swap ⟨0, by decide⟩),
   opAt 2737 .DIV,
   pushAt 2738 1 1,
   opAt 2739 .ADD,
   pushAt 2740 2 1600,
   opAt 2741 .MSTORE,
   opAt 2742 (.Dup ⟨0, by decide⟩),
   pushAt 2743 0 0,
   opAt 2744 .SUB,
   opAt 2745 (.Dup ⟨1, by decide⟩),
   opAt 2746 (.Swap ⟨0, by decide⟩),
   opAt 2747 .MOD,
   pushAt 2748 2 1632,
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
   pushAt 2795 2 1664,
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
   pushAt 2804 2 4047,
   opAt 2805 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2806 (.Dup ⟨1, by decide⟩),
   pushAt 2807 2 512,
   pushAt 2808 2 2080,
   opAt 2809 .MCOPY,
   pushAt 2810 0 0,
   pushAt 2811 2 2880,
   opAt 2812 .MLOAD,
   opAt 2813 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2814 2 512,
   opAt 2815 .MLOAD,
   pushAt 2816 2 1536,
   opAt 2817 .MLOAD,
   opAt 2818 (.Dup ⟨0, by decide⟩),
   opAt 2819 (.Dup ⟨2, by decide⟩),
   opAt 2820 .DIV,
   opAt 2821 (.Swap ⟨1, by decide⟩),
   opAt 2822 .MOD,
   pushAt 2823 2 1600,
   opAt 2824 .MLOAD,
   opAt 2825 .MUL,
   pushAt 2826 2 544,
   opAt 2827 .MLOAD,
   pushAt 2828 2 1536,
   opAt 2829 .MLOAD,
   opAt 2830 (.Swap ⟨0, by decide⟩),
   opAt 2831 .DIV,
   opAt 2832 .ADD,
   pushAt 2833 2 1568,
   opAt 2834 .MLOAD,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   pushAt 2836 2 1632,
   opAt 2837 .MLOAD,
   opAt 2838 (.Dup ⟨4, by decide⟩),
   opAt 2839 .MULMOD,
   opAt 2840 (.Dup ⟨2, by decide⟩),
   opAt 2841 .ADDMOD,
   opAt 2842 (.Swap ⟨0, by decide⟩),
   opAt 2843 .SUB,
   pushAt 2844 2 1664,
   opAt 2845 .MLOAD,
   opAt 2846 .MUL,
   opAt 2847 (.Dup ⟨0, by decide⟩),
   pushAt 2848 0 0,
   opAt 2849 .MLOAD,
   opAt 2850 .MUL,
   pushAt 2851 2 544,
   opAt 2852 .MLOAD,
   opAt 2853 .SUB,
   pushAt 2854 1 32,
   opAt 2855 .MLOAD,
   pushAt 2856 1 128,
   opAt 2857 .SHR,
   opAt 2858 (.Dup ⟨2, by decide⟩),
   pushAt 2859 1 128,
   opAt 2860 .SHR,
   opAt 2861 .MUL,
   opAt 2862 .GT,
   opAt 2863 (.Swap ⟨0, by decide⟩),
   opAt 2864 .SUB,
   opAt 2865 (.Swap ⟨0, by decide⟩),
   pushAt 2866 2 1568,
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
   pushAt 2874 1 31,
   opAt 2875 .NOT,
   pushAt 2876 2 2880,
   opAt 2877 .MLOAD,
   pushAt 2878 2 2848,
   opAt 2879 .MLOAD,
   pushAt 2880 2 1280,
   opAt 2881 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2882 .JUMPDEST,
   opAt 2883 (.Dup ⟨0, by decide⟩),
   opAt 2884 .MLOAD,
   pushAt 2885 0 0,
   opAt 2886 .NOT,
   opAt 2887 (.Dup ⟨6, by decide⟩),
   opAt 2888 (.Dup ⟨2, by decide⟩),
   opAt 2889 .MUL,
   opAt 2890 (.Swap ⟨1, by decide⟩),
   opAt 2891 (.Dup ⟨7, by decide⟩),
   opAt 2892 .MULMOD,
   opAt 2893 (.Dup ⟨1, by decide⟩),
   opAt 2894 (.Dup ⟨1, by decide⟩),
   opAt 2895 .LT,
   opAt 2896 .SUB,
   opAt 2897 (.Dup ⟨5, by decide⟩),
   opAt 2898 (.Dup ⟨2, by decide⟩),
   opAt 2899 .ADD,
   opAt 2900 (.Dup ⟨0, by decide⟩),
   opAt 2901 (.Swap ⟨6, by decide⟩),
   opAt 2902 .GT,
   opAt 2903 .SUB,
   opAt 2904 .SUB,
   opAt 2905 (.Dup ⟨4, by decide⟩),
   opAt 2906 (.Dup ⟨3, by decide⟩),
   opAt 2907 .MLOAD,
   opAt 2908 .ADD,
   opAt 2909 (.Dup ⟨0, by decide⟩),
   opAt 2910 (.Swap ⟨5, by decide⟩),
   opAt 2911 .GT,
   opAt 2912 .ADD,
   opAt 2913 (.Swap ⟨3, by decide⟩),
   opAt 2914 (.Dup ⟨2, by decide⟩),
   opAt 2915 (.Dup ⟨4, by decide⟩),
   opAt 2916 .ADD,
   opAt 2917 (.Swap ⟨2, by decide⟩),
   opAt 2918 .MSTORE,
   opAt 2919 (.Dup ⟨2, by decide⟩),
   opAt 2920 .ADD,
   pushAt 2921 2 2080,
   opAt 2922 (.Dup ⟨2, by decide⟩),
   opAt 2923 .GT,
   pushAt 2924 2 3809,
   opAt 2925 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2926 .POP,
   opAt 2927 .POP,
   opAt 2928 .POP,
   pushAt 2929 2 2080,
   opAt 2930 .MLOAD,
   opAt 2931 (.Dup ⟨1, by decide⟩),
   opAt 2932 .ADD,
   opAt 2933 (.Dup ⟨1, by decide⟩),
   opAt 2934 (.Dup ⟨1, by decide⟩),
   opAt 2935 .LT,
   opAt 2936 (.Swap ⟨1, by decide⟩),
   opAt 2937 .POP,
   opAt 2938 (.Dup ⟨2, by decide⟩),
   opAt 2939 (.Dup ⟨1, by decide⟩),
   opAt 2940 .LT,
   opAt 2941 (.Swap ⟨0, by decide⟩),
   opAt 2942 (.Dup ⟨3, by decide⟩),
   opAt 2943 (.Swap ⟨0, by decide⟩),
   opAt 2944 .SUB,
   opAt 2945 (.Dup ⟨0, by decide⟩),
   pushAt 2946 2 2080,
   opAt 2947 .MSTORE,
   opAt 2948 .POP,
   opAt 2949 .GT,
   opAt 2950 (.Swap ⟨0, by decide⟩),
   opAt 2951 .POP,
   opAt 2952 .ISZERO,
   pushAt 2953 2 3959,
   opAt 2954 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2955 .JUMPDEST,
   pushAt 2956 0 0,
   pushAt 2957 2 2880,
   opAt 2958 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2959 .JUMPDEST,
   opAt 2960 (.Dup ⟨0, by decide⟩),
   opAt 2961 .MLOAD,
   opAt 2962 (.Dup ⟨1, by decide⟩),
   pushAt 2963 2 2112,
   opAt 2964 (.Swap ⟨0, by decide⟩),
   opAt 2965 .SUB,
   opAt 2966 .MLOAD,
   opAt 2967 (.Dup ⟨1, by decide⟩),
   opAt 2968 .ADD,
   opAt 2969 (.Dup ⟨0, by decide⟩),
   opAt 2970 (.Dup ⟨2, by decide⟩),
   opAt 2971 .GT,
   opAt 2972 (.Swap ⟨1, by decide⟩),
   opAt 2973 .POP,
   opAt 2974 (.Dup ⟨3, by decide⟩),
   opAt 2975 .ADD,
   opAt 2976 (.Dup ⟨0, by decide⟩),
   opAt 2977 (.Dup ⟨4, by decide⟩),
   opAt 2978 .GT,
   opAt 2979 (.Swap ⟨3, by decide⟩),
   opAt 2980 .POP,
   opAt 2981 (.Dup ⟨2, by decide⟩),
   opAt 2982 .MSTORE,
   opAt 2983 (.Swap ⟨0, by decide⟩),
   opAt 2984 (.Swap ⟨1, by decide⟩),
   opAt 2985 .OR,
   opAt 2986 (.Swap ⟨0, by decide⟩),
   pushAt 2987 1 31,
   opAt 2988 .NOT,
   opAt 2989 .ADD,
   pushAt 2990 2 2111,
   opAt 2991 (.Dup ⟨1, by decide⟩),
   opAt 2992 .GT,
   pushAt 2993 2 3898,
   opAt 2994 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2995 .POP,
   pushAt 2996 2 2080,
   opAt 2997 .MLOAD,
   opAt 2998 (.Dup ⟨1, by decide⟩),
   opAt 2999 .ADD,
   opAt 3000 (.Dup ⟨0, by decide⟩),
   pushAt 3001 2 2080,
   opAt 3002 .MSTORE,
   opAt 3003 .LT,
   opAt 3004 .ISZERO,
   pushAt 3005 2 3892,
   opAt 3006 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3007 .JUMPDEST,
   pushAt 3008 2 2080,
   opAt 3009 .MLOAD,
   opAt 3010 .ISZERO,
   pushAt 3011 2 4027,
   opAt 3012 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3013 0 0,
   pushAt 3014 2 2880,
   opAt 3015 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3016 .JUMPDEST,
   opAt 3017 (.Dup ⟨0, by decide⟩),
   opAt 3018 .MLOAD,
   pushAt 3019 2 2112,
   opAt 3020 (.Dup ⟨2, by decide⟩),
   opAt 3021 .SUB,
   opAt 3022 .MLOAD,
   opAt 3023 (.Dup ⟨1, by decide⟩),
   opAt 3024 (.Dup ⟨1, by decide⟩),
   opAt 3025 .GT,
   opAt 3026 (.Swap ⟨1, by decide⟩),
   opAt 3027 .SUB,
   opAt 3028 (.Dup ⟨3, by decide⟩),
   opAt 3029 (.Dup ⟨1, by decide⟩),
   opAt 3030 .LT,
   opAt 3031 (.Swap ⟨0, by decide⟩),
   opAt 3032 (.Dup ⟨4, by decide⟩),
   opAt 3033 (.Swap ⟨0, by decide⟩),
   opAt 3034 .SUB,
   opAt 3035 (.Dup ⟨3, by decide⟩),
   opAt 3036 .MSTORE,
   opAt 3037 .OR,
   opAt 3038 (.Swap ⟨1, by decide⟩),
   opAt 3039 .POP,
   pushAt 3040 1 31,
   opAt 3041 .NOT,
   opAt 3042 .ADD,
   pushAt 3043 2 2111,
   opAt 3044 (.Dup ⟨1, by decide⟩),
   opAt 3045 .GT,
   pushAt 3046 2 3974,
   opAt 3047 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3048 .POP,
   pushAt 3049 2 2080,
   opAt 3050 .MLOAD,
   opAt 3051 .SUB,
   pushAt 3052 2 2080,
   opAt 3053 .MSTORE,
   pushAt 3054 2 3959,
   opAt 3055 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3056 .JUMPDEST,
   pushAt 3057 2 4038,
   pushAt 3058 2 512,
   pushAt 3059 2 4898,
   opAt 3060 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3061 .JUMPDEST,
   pushAt 3062 1 1,
   opAt 3063 (.Swap ⟨0, by decide⟩),
   opAt 3064 .SUB,
   pushAt 3065 2 3690,
   opAt 3066 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3067 .JUMPDEST,
   opAt 3068 .POP,
   pushAt 3069 2 3324,
   opAt 3070 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3809 = true :=
  Artifact.isValidJumpDest_index 2882 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3892 = true :=
  Artifact.isValidJumpDest_index 2955 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3898 = true :=
  Artifact.isValidJumpDest_index 2959 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3959 = true :=
  Artifact.isValidJumpDest_index 3007 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3974 = true :=
  Artifact.isValidJumpDest_index 3016 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4027 = true :=
  Artifact.isValidJumpDest_index 3056 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4038 = true :=
  Artifact.isValidJumpDest_index 3061 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4047 = true :=
  Artifact.isValidJumpDest_index 3067 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
