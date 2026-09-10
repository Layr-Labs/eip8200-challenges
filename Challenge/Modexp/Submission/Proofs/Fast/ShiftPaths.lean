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
  [opAt 2702 .JUMPDEST,
   opAt 2703 (.Dup ⟨0, by decide⟩),
   opAt 2704 (.Dup ⟨3, by decide⟩),
   opAt 2705 .EQ,
   pushAt 2706 0 0,
   opAt 2707 .MLOAD,
   pushAt 2708 1 255,
   opAt 2709 .SHR,
   opAt 2710 .AND,
   opAt 2711 .ISZERO,
   pushAt 2712 2 3628,
   opAt 2713 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2714 (.Dup ⟨0, by decide⟩),
   pushAt 2715 1 96,
   pushAt 2716 2 1024,
   opAt 2717 .CALLDATACOPY,
   opAt 2718 (.Dup ⟨0, by decide⟩),
   pushAt 2719 1 96,
   pushAt 2720 2 8256,
   opAt 2721 .CALLDATACOPY,
   pushAt 2722 0 0,
   pushAt 2723 2 8224,
   opAt 2724 .MSTORE,
   pushAt 2725 2 3633,
   pushAt 2726 2 2048,
   pushAt 2727 2 2220,
   opAt 2728 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2729 .JUMPDEST,
   pushAt 2730 2 1526,
   opAt 2731 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2732 .JUMPDEST,
   pushAt 2733 1 1,
   pushAt 2734 2 9408,
   opAt 2735 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2736 .JUMPDEST,
   opAt 2737 (.Dup ⟨0, by decide⟩),
   opAt 2738 .MLOAD,
   opAt 2739 .NOT,
   opAt 2740 (.Dup ⟨2, by decide⟩),
   opAt 2741 .ADD,
   opAt 2742 (.Dup ⟨2, by decide⟩),
   opAt 2743 (.Dup ⟨1, by decide⟩),
   opAt 2744 .LT,
   opAt 2745 (.Swap ⟨2, by decide⟩),
   opAt 2746 .POP,
   opAt 2747 (.Dup ⟨1, by decide⟩),
   pushAt 2748 2 5120,
   opAt 2749 .ADD,
   opAt 2750 .MSTORE,
   opAt 2751 (.Dup ⟨0, by decide⟩),
   opAt 2752 .ISZERO,
   pushAt 2753 2 3671,
   opAt 2754 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2755 1 31,
   opAt 2756 .NOT,
   opAt 2757 .ADD,
   pushAt 2758 2 3640,
   opAt 2759 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2760 .JUMPDEST,
   opAt 2761 .POP,
   opAt 2762 .POP,
   pushAt 2763 0 0,
   opAt 2764 .MLOAD,
   opAt 2765 (.Dup ⟨0, by decide⟩),
   pushAt 2766 0 0,
   opAt 2767 .SUB,
   opAt 2768 (.Dup ⟨1, by decide⟩),
   opAt 2769 .AND,
   opAt 2770 (.Dup ⟨0, by decide⟩),
   pushAt 2771 2 6144,
   opAt 2772 .MSTORE,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   opAt 2774 (.Dup ⟨2, by decide⟩),
   opAt 2775 .DIV,
   opAt 2776 (.Dup ⟨0, by decide⟩),
   pushAt 2777 2 6176,
   opAt 2778 .MSTORE,
   opAt 2779 (.Dup ⟨1, by decide⟩),
   pushAt 2780 0 0,
   opAt 2781 .SUB,
   opAt 2782 (.Dup ⟨2, by decide⟩),
   opAt 2783 (.Swap ⟨0, by decide⟩),
   opAt 2784 .DIV,
   pushAt 2785 1 1,
   opAt 2786 .ADD,
   pushAt 2787 2 6208,
   opAt 2788 .MSTORE,
   opAt 2789 (.Dup ⟨0, by decide⟩),
   pushAt 2790 0 0,
   opAt 2791 .SUB,
   opAt 2792 (.Dup ⟨1, by decide⟩),
   opAt 2793 (.Swap ⟨0, by decide⟩),
   opAt 2794 .MOD,
   pushAt 2795 2 6240,
   opAt 2796 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2797 (.Dup ⟨0, by decide⟩),
   pushAt 2798 1 2,
   opAt 2799 .SUB,
   opAt 2800 (.Dup ⟨0, by decide⟩),
   opAt 2801 (.Dup ⟨2, by decide⟩),
   opAt 2802 .MUL,
   pushAt 2803 1 2,
   opAt 2804 .SUB,
   opAt 2805 .MUL,
   opAt 2806 (.Dup ⟨0, by decide⟩),
   opAt 2807 (.Dup ⟨2, by decide⟩),
   opAt 2808 .MUL,
   pushAt 2809 1 2,
   opAt 2810 .SUB,
   opAt 2811 .MUL,
   opAt 2812 (.Dup ⟨0, by decide⟩),
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 .MUL,
   pushAt 2815 1 2,
   opAt 2816 .SUB,
   opAt 2817 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2818 (.Dup ⟨0, by decide⟩),
   opAt 2819 (.Dup ⟨2, by decide⟩),
   opAt 2820 .MUL,
   pushAt 2821 1 2,
   opAt 2822 .SUB,
   opAt 2823 .MUL,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   opAt 2825 (.Dup ⟨2, by decide⟩),
   opAt 2826 .MUL,
   pushAt 2827 1 2,
   opAt 2828 .SUB,
   opAt 2829 .MUL,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 (.Dup ⟨2, by decide⟩),
   opAt 2832 .MUL,
   pushAt 2833 1 2,
   opAt 2834 .SUB,
   opAt 2835 .MUL,
   opAt 2836 (.Dup ⟨0, by decide⟩),
   opAt 2837 (.Dup ⟨2, by decide⟩),
   opAt 2838 .MUL,
   pushAt 2839 1 2,
   opAt 2840 .SUB,
   opAt 2841 .MUL,
   pushAt 2842 2 6272,
   opAt 2843 .MSTORE,
   opAt 2844 .POP,
   opAt 2845 .POP,
   opAt 2846 .POP,
   opAt 2847 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2848 .JUMPDEST,
   opAt 2849 (.Dup ⟨0, by decide⟩),
   opAt 2850 .ISZERO,
   pushAt 2851 2 4131,
   opAt 2852 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2853 (.Dup ⟨1, by decide⟩),
   pushAt 2854 2 2048,
   pushAt 2855 2 8224,
   opAt 2856 .MCOPY,
   pushAt 2857 0 0,
   pushAt 2858 2 9440,
   opAt 2859 .MLOAD,
   opAt 2860 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2861 2 2048,
   opAt 2862 .MLOAD,
   pushAt 2863 2 6144,
   opAt 2864 .MLOAD,
   opAt 2865 (.Dup ⟨0, by decide⟩),
   opAt 2866 (.Dup ⟨2, by decide⟩),
   opAt 2867 .DIV,
   opAt 2868 (.Swap ⟨1, by decide⟩),
   opAt 2869 .MOD,
   pushAt 2870 2 6208,
   opAt 2871 .MLOAD,
   opAt 2872 .MUL,
   pushAt 2873 2 2080,
   opAt 2874 .MLOAD,
   pushAt 2875 2 6144,
   opAt 2876 .MLOAD,
   opAt 2877 (.Swap ⟨0, by decide⟩),
   opAt 2878 .DIV,
   opAt 2879 .ADD,
   pushAt 2880 2 6176,
   opAt 2881 .MLOAD,
   opAt 2882 (.Dup ⟨0, by decide⟩),
   pushAt 2883 2 6240,
   opAt 2884 .MLOAD,
   opAt 2885 (.Dup ⟨4, by decide⟩),
   opAt 2886 .MULMOD,
   opAt 2887 (.Dup ⟨2, by decide⟩),
   opAt 2888 .ADDMOD,
   opAt 2889 (.Swap ⟨0, by decide⟩),
   opAt 2890 .SUB,
   pushAt 2891 2 6272,
   opAt 2892 .MLOAD,
   opAt 2893 .MUL,
   opAt 2894 (.Dup ⟨0, by decide⟩),
   pushAt 2895 0 0,
   opAt 2896 .MLOAD,
   opAt 2897 .MUL,
   pushAt 2898 2 2080,
   opAt 2899 .MLOAD,
   opAt 2900 .SUB,
   pushAt 2901 1 32,
   opAt 2902 .MLOAD,
   opAt 2903 .GT,
   opAt 2904 (.Dup ⟨1, by decide⟩),
   pushAt 2905 0 0,
   opAt 2906 .LT,
   opAt 2907 .AND,
   opAt 2908 (.Swap ⟨0, by decide⟩),
   opAt 2909 .SUB,
   opAt 2910 (.Swap ⟨0, by decide⟩),
   pushAt 2911 2 6176,
   opAt 2912 .MLOAD,
   opAt 2913 .GT,
   opAt 2914 .ISZERO,
   pushAt 2915 0 0,
   opAt 2916 .SUB,
   opAt 2917 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2918 0 0,
   pushAt 2919 2 9440,
   opAt 2920 .MLOAD,
   pushAt 2921 2 9408,
   opAt 2922 .MLOAD,
   pushAt 2923 2 5120,
   opAt 2924 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2925 .JUMPDEST,
   opAt 2926 (.Dup ⟨0, by decide⟩),
   opAt 2927 .MLOAD,
   pushAt 2928 0 0,
   opAt 2929 .NOT,
   opAt 2930 (.Dup ⟨5, by decide⟩),
   opAt 2931 (.Dup ⟨2, by decide⟩),
   opAt 2932 .MUL,
   opAt 2933 (.Swap ⟨1, by decide⟩),
   opAt 2934 (.Dup ⟨6, by decide⟩),
   opAt 2935 .MULMOD,
   opAt 2936 (.Dup ⟨1, by decide⟩),
   opAt 2937 (.Dup ⟨1, by decide⟩),
   opAt 2938 .LT,
   opAt 2939 .SUB,
   opAt 2940 (.Dup ⟨4, by decide⟩),
   opAt 2941 (.Dup ⟨2, by decide⟩),
   opAt 2942 .ADD,
   opAt 2943 (.Dup ⟨0, by decide⟩),
   opAt 2944 (.Swap ⟨5, by decide⟩),
   opAt 2945 .GT,
   opAt 2946 .SUB,
   opAt 2947 .SUB,
   opAt 2948 (.Dup ⟨3, by decide⟩),
   opAt 2949 (.Dup ⟨3, by decide⟩),
   opAt 2950 .MLOAD,
   opAt 2951 .ADD,
   opAt 2952 (.Dup ⟨0, by decide⟩),
   opAt 2953 (.Swap ⟨4, by decide⟩),
   opAt 2954 .GT,
   opAt 2955 .ADD,
   opAt 2956 (.Swap ⟨2, by decide⟩),
   opAt 2957 (.Dup ⟨2, by decide⟩),
   pushAt 2958 1 31,
   opAt 2959 .NOT,
   opAt 2960 .ADD,
   opAt 2961 (.Swap ⟨2, by decide⟩),
   opAt 2962 .MSTORE,
   pushAt 2963 1 31,
   opAt 2964 .NOT,
   opAt 2965 .ADD,
   pushAt 2966 2 8224,
   opAt 2967 (.Dup ⟨2, by decide⟩),
   opAt 2968 .GT,
   pushAt 2969 2 3890,
   opAt 2970 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2971 .POP,
   opAt 2972 .POP,
   pushAt 2973 2 8224,
   opAt 2974 .MLOAD,
   opAt 2975 (.Dup ⟨1, by decide⟩),
   opAt 2976 .ADD,
   opAt 2977 (.Dup ⟨1, by decide⟩),
   opAt 2978 (.Dup ⟨1, by decide⟩),
   opAt 2979 .LT,
   opAt 2980 (.Swap ⟨1, by decide⟩),
   opAt 2981 .POP,
   opAt 2982 (.Dup ⟨2, by decide⟩),
   opAt 2983 (.Dup ⟨1, by decide⟩),
   opAt 2984 .LT,
   opAt 2985 (.Swap ⟨0, by decide⟩),
   opAt 2986 (.Dup ⟨3, by decide⟩),
   opAt 2987 (.Swap ⟨0, by decide⟩),
   opAt 2988 .SUB,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   pushAt 2990 2 8224,
   opAt 2991 .MSTORE,
   opAt 2992 .POP,
   opAt 2993 .GT,
   opAt 2994 (.Swap ⟨0, by decide⟩),
   opAt 2995 .POP,
   opAt 2996 .ISZERO,
   pushAt 2997 2 4043,
   opAt 2998 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2999 .JUMPDEST,
   pushAt 3000 0 0,
   pushAt 3001 2 9440,
   opAt 3002 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3003 .JUMPDEST,
   opAt 3004 (.Dup ⟨0, by decide⟩),
   opAt 3005 .MLOAD,
   opAt 3006 (.Dup ⟨1, by decide⟩),
   pushAt 3007 2 8256,
   opAt 3008 (.Swap ⟨0, by decide⟩),
   opAt 3009 .SUB,
   opAt 3010 .MLOAD,
   opAt 3011 (.Dup ⟨1, by decide⟩),
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨2, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 (.Swap ⟨1, by decide⟩),
   opAt 3017 .POP,
   opAt 3018 (.Dup ⟨3, by decide⟩),
   opAt 3019 .ADD,
   opAt 3020 (.Dup ⟨0, by decide⟩),
   opAt 3021 (.Dup ⟨4, by decide⟩),
   opAt 3022 .GT,
   opAt 3023 (.Swap ⟨3, by decide⟩),
   opAt 3024 .POP,
   opAt 3025 (.Dup ⟨2, by decide⟩),
   opAt 3026 .MSTORE,
   opAt 3027 (.Swap ⟨0, by decide⟩),
   opAt 3028 (.Swap ⟨1, by decide⟩),
   opAt 3029 .OR,
   opAt 3030 (.Swap ⟨0, by decide⟩),
   pushAt 3031 1 31,
   opAt 3032 .NOT,
   opAt 3033 .ADD,
   pushAt 3034 2 8255,
   opAt 3035 (.Dup ⟨1, by decide⟩),
   opAt 3036 .GT,
   pushAt 3037 2 3982,
   opAt 3038 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3039 .POP,
   pushAt 3040 2 8224,
   opAt 3041 .MLOAD,
   opAt 3042 (.Dup ⟨1, by decide⟩),
   opAt 3043 .ADD,
   opAt 3044 (.Dup ⟨0, by decide⟩),
   pushAt 3045 2 8224,
   opAt 3046 .MSTORE,
   opAt 3047 .LT,
   opAt 3048 .ISZERO,
   pushAt 3049 2 3976,
   opAt 3050 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3051 .JUMPDEST,
   pushAt 3052 2 8224,
   opAt 3053 .MLOAD,
   opAt 3054 .ISZERO,
   pushAt 3055 2 4111,
   opAt 3056 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3057 0 0,
   pushAt 3058 2 9440,
   opAt 3059 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3060 .JUMPDEST,
   opAt 3061 (.Dup ⟨0, by decide⟩),
   opAt 3062 .MLOAD,
   pushAt 3063 2 8256,
   opAt 3064 (.Dup ⟨2, by decide⟩),
   opAt 3065 .SUB,
   opAt 3066 .MLOAD,
   opAt 3067 (.Dup ⟨1, by decide⟩),
   opAt 3068 (.Dup ⟨1, by decide⟩),
   opAt 3069 .GT,
   opAt 3070 (.Swap ⟨1, by decide⟩),
   opAt 3071 .SUB,
   opAt 3072 (.Dup ⟨3, by decide⟩),
   opAt 3073 (.Dup ⟨1, by decide⟩),
   opAt 3074 .LT,
   opAt 3075 (.Swap ⟨0, by decide⟩),
   opAt 3076 (.Dup ⟨4, by decide⟩),
   opAt 3077 (.Swap ⟨0, by decide⟩),
   opAt 3078 .SUB,
   opAt 3079 (.Dup ⟨3, by decide⟩),
   opAt 3080 .MSTORE,
   opAt 3081 .OR,
   opAt 3082 (.Swap ⟨1, by decide⟩),
   opAt 3083 .POP,
   pushAt 3084 1 31,
   opAt 3085 .NOT,
   opAt 3086 .ADD,
   pushAt 3087 2 8255,
   opAt 3088 (.Dup ⟨1, by decide⟩),
   opAt 3089 .GT,
   pushAt 3090 2 4058,
   opAt 3091 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3092 .POP,
   pushAt 3093 2 8224,
   opAt 3094 .MLOAD,
   opAt 3095 .SUB,
   pushAt 3096 2 8224,
   opAt 3097 .MSTORE,
   pushAt 3098 2 4043,
   opAt 3099 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3100 .JUMPDEST,
   pushAt 3101 2 4122,
   pushAt 3102 2 2048,
   pushAt 3103 2 2220,
   opAt 3104 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3105 .JUMPDEST,
   pushAt 3106 1 1,
   opAt 3107 (.Swap ⟨0, by decide⟩),
   opAt 3108 .SUB,
   pushAt 3109 2 3778,
   opAt 3110 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3111 .JUMPDEST,
   opAt 3112 .POP,
   pushAt 3113 2 1698,
   opAt 3114 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3584 = true :=
  Artifact.isValidJumpDest_index 2702 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3628 = true :=
  Artifact.isValidJumpDest_index 2729 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3633 = true :=
  Artifact.isValidJumpDest_index 2732 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3640 = true :=
  Artifact.isValidJumpDest_index 2736 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3671 = true :=
  Artifact.isValidJumpDest_index 2760 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3778 = true :=
  Artifact.isValidJumpDest_index 2848 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3890 = true :=
  Artifact.isValidJumpDest_index 2925 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3976 = true :=
  Artifact.isValidJumpDest_index 2999 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3982 = true :=
  Artifact.isValidJumpDest_index 3003 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4043 = true :=
  Artifact.isValidJumpDest_index 3051 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4058 = true :=
  Artifact.isValidJumpDest_index 3060 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4111 = true :=
  Artifact.isValidJumpDest_index 3100 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4122 = true :=
  Artifact.isValidJumpDest_index 3105 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4131 = true :=
  Artifact.isValidJumpDest_index 3111 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
