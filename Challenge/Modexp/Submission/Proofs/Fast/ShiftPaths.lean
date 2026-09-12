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
  [opAt 2594 .JUMPDEST,
   opAt 2595 (.Dup ⟨0, by decide⟩),
   opAt 2596 (.Dup ⟨3, by decide⟩),
   opAt 2597 .EQ,
   pushAt 2598 0 0,
   opAt 2599 .MLOAD,
   pushAt 2600 1 255,
   opAt 2601 .SHR,
   opAt 2602 .AND,
   opAt 2603 .ISZERO,
   pushAt 2604 2 3463,
   opAt 2605 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2606 (.Dup ⟨0, by decide⟩),
   pushAt 2607 1 96,
   pushAt 2608 2 256,
   opAt 2609 .CALLDATACOPY,
   opAt 2610 (.Dup ⟨0, by decide⟩),
   pushAt 2611 1 96,
   pushAt 2612 2 4160,
   opAt 2613 .CALLDATACOPY,
   pushAt 2614 0 0,
   pushAt 2615 2 4128,
   opAt 2616 .MSTORE,
   pushAt 2617 2 3480,
   pushAt 2618 2 512,
   pushAt 2619 2 4874,
   opAt 2620 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2621 .JUMPDEST,
   pushAt 2622 1 1,
   pushAt 2623 2 1024,
   opAt 2624 .MSTORE,
   pushAt 2625 2 1430,
   pushAt 2626 2 1024,
   pushAt 2627 2 2211,
   opAt 2628 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2629 .JUMPDEST,
   pushAt 2630 1 1,
   pushAt 2631 2 5312,
   opAt 2632 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2633 .JUMPDEST,
   opAt 2634 (.Dup ⟨0, by decide⟩),
   opAt 2635 .MLOAD,
   opAt 2636 .NOT,
   opAt 2637 (.Dup ⟨2, by decide⟩),
   opAt 2638 .ADD,
   opAt 2639 (.Dup ⟨2, by decide⟩),
   opAt 2640 (.Dup ⟨1, by decide⟩),
   opAt 2641 .LT,
   opAt 2642 (.Swap ⟨2, by decide⟩),
   opAt 2643 .POP,
   opAt 2644 (.Dup ⟨1, by decide⟩),
   pushAt 2645 2 1280,
   opAt 2646 .ADD,
   opAt 2647 .MSTORE,
   opAt 2648 (.Dup ⟨0, by decide⟩),
   opAt 2649 .ISZERO,
   pushAt 2650 2 3518,
   opAt 2651 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2652 1 31,
   opAt 2653 .NOT,
   opAt 2654 .ADD,
   pushAt 2655 2 3487,
   opAt 2656 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2657 .JUMPDEST,
   opAt 2658 .POP,
   opAt 2659 .POP,
   pushAt 2660 0 0,
   opAt 2661 .MLOAD,
   opAt 2662 (.Dup ⟨0, by decide⟩),
   pushAt 2663 0 0,
   opAt 2664 .SUB,
   opAt 2665 (.Dup ⟨1, by decide⟩),
   opAt 2666 .AND,
   opAt 2667 (.Dup ⟨0, by decide⟩),
   pushAt 2668 2 1536,
   opAt 2669 .MSTORE,
   opAt 2670 (.Dup ⟨0, by decide⟩),
   opAt 2671 (.Dup ⟨2, by decide⟩),
   opAt 2672 .DIV,
   opAt 2673 (.Dup ⟨0, by decide⟩),
   pushAt 2674 2 1568,
   opAt 2675 .MSTORE,
   opAt 2676 (.Dup ⟨1, by decide⟩),
   pushAt 2677 0 0,
   opAt 2678 .SUB,
   opAt 2679 (.Dup ⟨2, by decide⟩),
   opAt 2680 (.Swap ⟨0, by decide⟩),
   opAt 2681 .DIV,
   pushAt 2682 1 1,
   opAt 2683 .ADD,
   pushAt 2684 2 1600,
   opAt 2685 .MSTORE,
   opAt 2686 (.Dup ⟨0, by decide⟩),
   pushAt 2687 0 0,
   opAt 2688 .SUB,
   opAt 2689 (.Dup ⟨1, by decide⟩),
   opAt 2690 (.Swap ⟨0, by decide⟩),
   opAt 2691 .MOD,
   pushAt 2692 2 1632,
   opAt 2693 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2694 (.Dup ⟨0, by decide⟩),
   pushAt 2695 1 2,
   opAt 2696 .SUB,
   opAt 2697 (.Dup ⟨0, by decide⟩),
   opAt 2698 (.Dup ⟨2, by decide⟩),
   opAt 2699 .MUL,
   pushAt 2700 1 2,
   opAt 2701 .SUB,
   opAt 2702 .MUL,
   opAt 2703 (.Dup ⟨0, by decide⟩),
   opAt 2704 (.Dup ⟨2, by decide⟩),
   opAt 2705 .MUL,
   pushAt 2706 1 2,
   opAt 2707 .SUB,
   opAt 2708 .MUL,
   opAt 2709 (.Dup ⟨0, by decide⟩),
   opAt 2710 (.Dup ⟨2, by decide⟩),
   opAt 2711 .MUL,
   pushAt 2712 1 2,
   opAt 2713 .SUB,
   opAt 2714 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2715 (.Dup ⟨0, by decide⟩),
   opAt 2716 (.Dup ⟨2, by decide⟩),
   opAt 2717 .MUL,
   pushAt 2718 1 2,
   opAt 2719 .SUB,
   opAt 2720 .MUL,
   opAt 2721 (.Dup ⟨0, by decide⟩),
   opAt 2722 (.Dup ⟨2, by decide⟩),
   opAt 2723 .MUL,
   pushAt 2724 1 2,
   opAt 2725 .SUB,
   opAt 2726 .MUL,
   opAt 2727 (.Dup ⟨0, by decide⟩),
   opAt 2728 (.Dup ⟨2, by decide⟩),
   opAt 2729 .MUL,
   pushAt 2730 1 2,
   opAt 2731 .SUB,
   opAt 2732 .MUL,
   opAt 2733 (.Dup ⟨0, by decide⟩),
   opAt 2734 (.Dup ⟨2, by decide⟩),
   opAt 2735 .MUL,
   pushAt 2736 1 2,
   opAt 2737 .SUB,
   opAt 2738 .MUL,
   pushAt 2739 2 1664,
   opAt 2740 .MSTORE,
   opAt 2741 .POP,
   opAt 2742 .POP,
   opAt 2743 .POP,
   opAt 2744 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2756 .JUMPDEST,
   opAt 2757 (.Dup ⟨0, by decide⟩),
   opAt 2758 .ISZERO,
   pushAt 2759 2 4120,
   opAt 2760 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2761 (.Dup ⟨1, by decide⟩),
   pushAt 2762 2 512,
   pushAt 2763 2 4128,
   opAt 2764 .MCOPY,
   pushAt 2765 0 0,
   pushAt 2766 2 5344,
   opAt 2767 .MLOAD,
   opAt 2768 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2769 2 512,
   opAt 2770 .MLOAD,
   pushAt 2771 2 1536,
   opAt 2772 .MLOAD,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   opAt 2774 (.Dup ⟨2, by decide⟩),
   opAt 2775 .DIV,
   opAt 2776 (.Swap ⟨1, by decide⟩),
   opAt 2777 .MOD,
   pushAt 2778 2 1600,
   opAt 2779 .MLOAD,
   opAt 2780 .MUL,
   pushAt 2781 2 544,
   opAt 2782 .MLOAD,
   pushAt 2783 2 1536,
   opAt 2784 .MLOAD,
   opAt 2785 (.Swap ⟨0, by decide⟩),
   opAt 2786 .DIV,
   opAt 2787 .ADD,
   pushAt 2788 2 1568,
   opAt 2789 .MLOAD,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   pushAt 2791 2 1632,
   opAt 2792 .MLOAD,
   opAt 2793 (.Dup ⟨4, by decide⟩),
   opAt 2794 .MULMOD,
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .ADDMOD,
   opAt 2797 (.Swap ⟨0, by decide⟩),
   opAt 2798 .SUB,
   pushAt 2799 2 1664,
   opAt 2800 .MLOAD,
   opAt 2801 .MUL,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   pushAt 2803 0 0,
   opAt 2804 .MLOAD,
   opAt 2805 .MUL,
   pushAt 2806 2 544,
   opAt 2807 .MLOAD,
   opAt 2808 .SUB,
   pushAt 2809 1 32,
   opAt 2810 .MLOAD,
   pushAt 2811 1 128,
   opAt 2812 .SHR,
   opAt 2813 (.Dup ⟨2, by decide⟩),
   pushAt 2814 1 128,
   opAt 2815 .SHR,
   opAt 2816 .MUL,
   opAt 2817 .GT,
   opAt 2818 (.Swap ⟨0, by decide⟩),
   opAt 2819 .SUB,
   opAt 2820 (.Swap ⟨0, by decide⟩),
   pushAt 2821 2 1568,
   opAt 2822 .MLOAD,
   opAt 2823 .GT,
   opAt 2824 .ISZERO,
   pushAt 2825 0 0,
   opAt 2826 .SUB,
   opAt 2827 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2828 0 0,
   pushAt 2829 1 31,
   opAt 2830 .NOT,
   pushAt 2831 2 5344,
   opAt 2832 .MLOAD,
   pushAt 2833 2 5312,
   opAt 2834 .MLOAD,
   pushAt 2835 2 1280,
   opAt 2836 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2840 .JUMPDEST,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   opAt 2842 .MLOAD,
   pushAt 2843 0 0,
   opAt 2844 .NOT,
   opAt 2845 (.Dup ⟨6, by decide⟩),
   opAt 2846 (.Dup ⟨2, by decide⟩),
   opAt 2847 .MUL,
   opAt 2848 (.Swap ⟨1, by decide⟩),
   opAt 2849 (.Dup ⟨7, by decide⟩),
   opAt 2850 .MULMOD,
   opAt 2851 (.Dup ⟨1, by decide⟩),
   opAt 2852 (.Dup ⟨1, by decide⟩),
   opAt 2853 .LT,
   opAt 2854 .SUB,
   opAt 2855 (.Dup ⟨5, by decide⟩),
   opAt 2856 (.Dup ⟨2, by decide⟩),
   opAt 2857 .ADD,
   opAt 2858 (.Dup ⟨0, by decide⟩),
   opAt 2859 (.Swap ⟨6, by decide⟩),
   opAt 2860 .GT,
   opAt 2861 .SUB,
   opAt 2862 .SUB,
   opAt 2863 (.Dup ⟨4, by decide⟩),
   opAt 2864 (.Dup ⟨3, by decide⟩),
   opAt 2865 .MLOAD,
   opAt 2866 .ADD,
   opAt 2867 (.Dup ⟨0, by decide⟩),
   opAt 2868 (.Swap ⟨5, by decide⟩),
   opAt 2869 .GT,
   opAt 2870 .ADD,
   opAt 2871 (.Swap ⟨3, by decide⟩),
   opAt 2872 (.Dup ⟨2, by decide⟩),
   opAt 2873 (.Dup ⟨4, by decide⟩),
   opAt 2874 .ADD,
   opAt 2875 (.Swap ⟨2, by decide⟩),
   opAt 2876 .MSTORE,
   opAt 2877 (.Dup ⟨2, by decide⟩),
   opAt 2878 .ADD,
   pushAt 2996 2 4128,
   opAt 2997 (.Dup ⟨2, by decide⟩),
   opAt 2998 .GT,
   pushAt 2999 2 3766,
   opAt 3000 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3001 .POP,
   opAt 3002 .POP,
   opAt 3003 .POP,
   pushAt 3004 2 4128,
   opAt 3005 .MLOAD,
   opAt 3006 (.Dup ⟨1, by decide⟩),
   opAt 3007 .ADD,
   opAt 3008 (.Dup ⟨1, by decide⟩),
   opAt 3009 (.Dup ⟨1, by decide⟩),
   opAt 3010 .LT,
   opAt 3011 (.Swap ⟨1, by decide⟩),
   opAt 3012 .POP,
   opAt 3013 (.Dup ⟨2, by decide⟩),
   opAt 3014 (.Dup ⟨1, by decide⟩),
   opAt 3015 .LT,
   opAt 3016 (.Swap ⟨0, by decide⟩),
   opAt 3017 (.Dup ⟨3, by decide⟩),
   opAt 3018 (.Swap ⟨0, by decide⟩),
   opAt 3019 .SUB,
   opAt 3020 (.Dup ⟨0, by decide⟩),
   pushAt 3021 2 4128,
   opAt 3022 .MSTORE,
   opAt 3023 .POP,
   opAt 3024 .GT,
   opAt 3025 (.Swap ⟨0, by decide⟩),
   opAt 3026 .POP,
   opAt 3027 .ISZERO,
   pushAt 3028 2 4033,
   opAt 3029 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3030 .JUMPDEST,
   pushAt 3031 0 0,
   pushAt 3032 2 5344,
   opAt 3033 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3034 .JUMPDEST,
   opAt 3035 (.Dup ⟨0, by decide⟩),
   opAt 3036 .MLOAD,
   opAt 3037 (.Dup ⟨1, by decide⟩),
   pushAt 3038 2 4160,
   opAt 3039 (.Swap ⟨0, by decide⟩),
   opAt 3040 .SUB,
   opAt 3041 .MLOAD,
   opAt 3042 (.Dup ⟨1, by decide⟩),
   opAt 3043 .ADD,
   opAt 3044 (.Dup ⟨0, by decide⟩),
   opAt 3045 (.Dup ⟨2, by decide⟩),
   opAt 3046 .GT,
   opAt 3047 (.Swap ⟨1, by decide⟩),
   opAt 3048 .POP,
   opAt 3049 (.Dup ⟨3, by decide⟩),
   opAt 3050 .ADD,
   opAt 3051 (.Dup ⟨0, by decide⟩),
   opAt 3052 (.Dup ⟨4, by decide⟩),
   opAt 3053 .GT,
   opAt 3054 (.Swap ⟨3, by decide⟩),
   opAt 3055 .POP,
   opAt 3056 (.Dup ⟨2, by decide⟩),
   opAt 3057 .MSTORE,
   opAt 3058 (.Swap ⟨0, by decide⟩),
   opAt 3059 (.Swap ⟨1, by decide⟩),
   opAt 3060 .OR,
   opAt 3061 (.Swap ⟨0, by decide⟩),
   pushAt 3062 1 31,
   opAt 3063 .NOT,
   opAt 3064 .ADD,
   pushAt 3065 2 4159,
   opAt 3066 (.Dup ⟨1, by decide⟩),
   opAt 3067 .GT,
   pushAt 3068 2 3972,
   opAt 3069 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3070 .POP,
   pushAt 3071 2 4128,
   opAt 3072 .MLOAD,
   opAt 3073 (.Dup ⟨1, by decide⟩),
   opAt 3074 .ADD,
   opAt 3075 (.Dup ⟨0, by decide⟩),
   pushAt 3076 2 4128,
   opAt 3077 .MSTORE,
   opAt 3078 .LT,
   opAt 3079 .ISZERO,
   pushAt 3080 2 3966,
   opAt 3081 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3082 .JUMPDEST,
   pushAt 3083 2 4128,
   opAt 3084 .MLOAD,
   opAt 3085 .ISZERO,
   pushAt 3086 2 4101,
   opAt 3087 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3088 0 0,
   pushAt 3089 2 5344,
   opAt 3090 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3091 .JUMPDEST,
   opAt 3092 (.Dup ⟨0, by decide⟩),
   opAt 3093 .MLOAD,
   pushAt 3094 2 4160,
   opAt 3095 (.Dup ⟨2, by decide⟩),
   opAt 3096 .SUB,
   opAt 3097 .MLOAD,
   opAt 3098 (.Dup ⟨1, by decide⟩),
   opAt 3099 (.Dup ⟨1, by decide⟩),
   opAt 3100 .GT,
   opAt 3101 (.Swap ⟨1, by decide⟩),
   opAt 3102 .SUB,
   opAt 3103 (.Dup ⟨3, by decide⟩),
   opAt 3104 (.Dup ⟨1, by decide⟩),
   opAt 3105 .LT,
   opAt 3106 (.Swap ⟨0, by decide⟩),
   opAt 3107 (.Dup ⟨4, by decide⟩),
   opAt 3108 (.Swap ⟨0, by decide⟩),
   opAt 3109 .SUB,
   opAt 3110 (.Dup ⟨3, by decide⟩),
   opAt 3111 .MSTORE,
   opAt 3112 .OR,
   opAt 3113 (.Swap ⟨1, by decide⟩),
   opAt 3114 .POP,
   pushAt 3115 1 31,
   opAt 3116 .NOT,
   opAt 3117 .ADD,
   pushAt 3118 2 4159,
   opAt 3119 (.Dup ⟨1, by decide⟩),
   opAt 3120 .GT,
   pushAt 3121 2 4048,
   opAt 3122 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3123 .POP,
   pushAt 3124 2 4128,
   opAt 3125 .MLOAD,
   opAt 3126 .SUB,
   pushAt 3127 2 4128,
   opAt 3128 .MSTORE,
   pushAt 3129 2 4033,
   opAt 3130 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3131 .JUMPDEST,
   pushAt 3132 2 4112,
   pushAt 3133 2 512,
   pushAt 3134 2 4874,
   opAt 3135 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3136 .JUMPDEST,
   pushAt 3137 0 0,
   opAt 3138 .NOT,
   opAt 3139 .ADD,
   pushAt 3140 2 3642,
   opAt 3141 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3142 .JUMPDEST,
   opAt 3143 .POP,
   pushAt 3144 2 5248,
   opAt 3145 .MLOAD,
   pushAt 3146 2 1280,
   pushAt 3147 2 1024,
   opAt 3148 .MCOPY,
   pushAt 3149 2 3261,
   opAt 3150 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3419 = true :=
  Artifact.isValidJumpDest_index 2594 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3463 = true :=
  Artifact.isValidJumpDest_index 2621 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3480 = true :=
  Artifact.isValidJumpDest_index 2629 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3487 = true :=
  Artifact.isValidJumpDest_index 2633 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3518 = true :=
  Artifact.isValidJumpDest_index 2657 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3642 = true :=
  Artifact.isValidJumpDest_index 2756 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3766 = true :=
  Artifact.isValidJumpDest_index 2840 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3966 = true :=
  Artifact.isValidJumpDest_index 3030 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3972 = true :=
  Artifact.isValidJumpDest_index 3034 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4033 = true :=
  Artifact.isValidJumpDest_index 3082 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4048 = true :=
  Artifact.isValidJumpDest_index 3091 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4101 = true :=
  Artifact.isValidJumpDest_index 3131 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4112 = true :=
  Artifact.isValidJumpDest_index 3136 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4120 = true :=
  Artifact.isValidJumpDest_index 3142 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
