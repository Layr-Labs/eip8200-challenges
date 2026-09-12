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
  [opAt 2583 .JUMPDEST,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   opAt 2585 (.Dup ⟨3, by decide⟩),
   opAt 2586 .EQ,
   pushAt 2587 0 0,
   opAt 2588 .MLOAD,
   pushAt 2589 1 255,
   opAt 2590 .SHR,
   opAt 2591 .AND,
   opAt 2592 .ISZERO,
   pushAt 2593 2 3477,
   opAt 2594 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2595 (.Dup ⟨0, by decide⟩),
   pushAt 2596 1 96,
   pushAt 2597 2 256,
   opAt 2598 .CALLDATACOPY,
   opAt 2599 (.Dup ⟨0, by decide⟩),
   pushAt 2600 1 96,
   pushAt 2601 2 4160,
   opAt 2602 .CALLDATACOPY,
   pushAt 2603 0 0,
   pushAt 2604 2 4128,
   opAt 2605 .MSTORE,
   pushAt 2606 2 3494,
   pushAt 2607 2 512,
   pushAt 2608 2 4885,
   opAt 2609 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2610 .JUMPDEST,
   pushAt 2611 1 1,
   pushAt 2612 2 1024,
   opAt 2613 .MSTORE,
   pushAt 2614 2 1430,
   pushAt 2615 2 1024,
   pushAt 2616 2 2211,
   opAt 2617 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2618 .JUMPDEST,
   pushAt 2619 1 1,
   pushAt 2620 2 5312,
   opAt 2621 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2622 .JUMPDEST,
   opAt 2623 (.Dup ⟨0, by decide⟩),
   opAt 2624 .MLOAD,
   opAt 2625 .NOT,
   opAt 2626 (.Dup ⟨2, by decide⟩),
   opAt 2627 .ADD,
   opAt 2628 (.Dup ⟨2, by decide⟩),
   opAt 2629 (.Dup ⟨1, by decide⟩),
   opAt 2630 .LT,
   opAt 2631 (.Swap ⟨2, by decide⟩),
   opAt 2632 .POP,
   opAt 2633 (.Dup ⟨1, by decide⟩),
   pushAt 2634 2 1280,
   opAt 2635 .ADD,
   opAt 2636 .MSTORE,
   opAt 2637 (.Dup ⟨0, by decide⟩),
   opAt 2638 .ISZERO,
   pushAt 2639 2 3532,
   opAt 2640 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2641 1 31,
   opAt 2642 .NOT,
   opAt 2643 .ADD,
   pushAt 2644 2 3501,
   opAt 2645 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2646 .JUMPDEST,
   opAt 2647 .POP,
   opAt 2648 .POP,
   pushAt 2649 0 0,
   opAt 2650 .MLOAD,
   opAt 2651 (.Dup ⟨0, by decide⟩),
   pushAt 2652 0 0,
   opAt 2653 .SUB,
   opAt 2654 (.Dup ⟨1, by decide⟩),
   opAt 2655 .AND,
   opAt 2656 (.Dup ⟨0, by decide⟩),
   pushAt 2657 2 1536,
   opAt 2658 .MSTORE,
   opAt 2659 (.Dup ⟨0, by decide⟩),
   opAt 2660 (.Dup ⟨2, by decide⟩),
   opAt 2661 .DIV,
   opAt 2662 (.Dup ⟨0, by decide⟩),
   pushAt 2663 2 1568,
   opAt 2664 .MSTORE,
   opAt 2665 (.Dup ⟨1, by decide⟩),
   pushAt 2666 0 0,
   opAt 2667 .SUB,
   opAt 2668 (.Dup ⟨2, by decide⟩),
   opAt 2669 (.Swap ⟨0, by decide⟩),
   opAt 2670 .DIV,
   pushAt 2671 1 1,
   opAt 2672 .ADD,
   pushAt 2673 2 1600,
   opAt 2674 .MSTORE,
   opAt 2675 (.Dup ⟨0, by decide⟩),
   pushAt 2676 0 0,
   opAt 2677 .SUB,
   opAt 2678 (.Dup ⟨1, by decide⟩),
   opAt 2679 (.Swap ⟨0, by decide⟩),
   opAt 2680 .MOD,
   pushAt 2681 2 1632,
   opAt 2682 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2683 (.Dup ⟨0, by decide⟩),
   pushAt 2684 1 2,
   opAt 2685 .SUB,
   opAt 2686 (.Dup ⟨0, by decide⟩),
   opAt 2687 (.Dup ⟨2, by decide⟩),
   opAt 2688 .MUL,
   pushAt 2689 1 2,
   opAt 2690 .SUB,
   opAt 2691 .MUL,
   opAt 2692 (.Dup ⟨0, by decide⟩),
   opAt 2693 (.Dup ⟨2, by decide⟩),
   opAt 2694 .MUL,
   pushAt 2695 1 2,
   opAt 2696 .SUB,
   opAt 2697 .MUL,
   opAt 2698 (.Dup ⟨0, by decide⟩),
   opAt 2699 (.Dup ⟨2, by decide⟩),
   opAt 2700 .MUL,
   pushAt 2701 1 2,
   opAt 2702 .SUB,
   opAt 2703 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2704 (.Dup ⟨0, by decide⟩),
   opAt 2705 (.Dup ⟨2, by decide⟩),
   opAt 2706 .MUL,
   pushAt 2707 1 2,
   opAt 2708 .SUB,
   opAt 2709 .MUL,
   opAt 2710 (.Dup ⟨0, by decide⟩),
   opAt 2711 (.Dup ⟨2, by decide⟩),
   opAt 2712 .MUL,
   pushAt 2713 1 2,
   opAt 2714 .SUB,
   opAt 2715 .MUL,
   opAt 2716 (.Dup ⟨0, by decide⟩),
   opAt 2717 (.Dup ⟨2, by decide⟩),
   opAt 2718 .MUL,
   pushAt 2719 1 2,
   opAt 2720 .SUB,
   opAt 2721 .MUL,
   opAt 2722 (.Dup ⟨0, by decide⟩),
   opAt 2723 (.Dup ⟨2, by decide⟩),
   opAt 2724 .MUL,
   pushAt 2725 1 2,
   opAt 2726 .SUB,
   opAt 2727 .MUL,
   pushAt 2728 2 1664,
   opAt 2729 .MSTORE,
   opAt 2730 .POP,
   opAt 2731 .POP,
   opAt 2732 .POP,
   opAt 2733 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2745 .JUMPDEST,
   opAt 2746 (.Dup ⟨0, by decide⟩),
   opAt 2747 .ISZERO,
   pushAt 2748 2 4134,
   opAt 2749 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2750 (.Dup ⟨1, by decide⟩),
   pushAt 2751 2 512,
   pushAt 2752 2 4128,
   opAt 2753 .MCOPY,
   pushAt 2754 0 0,
   pushAt 2755 2 5344,
   opAt 2756 .MLOAD,
   opAt 2757 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2758 2 512,
   opAt 2759 .MLOAD,
   pushAt 2760 2 1536,
   opAt 2761 .MLOAD,
   opAt 2762 (.Dup ⟨0, by decide⟩),
   opAt 2763 (.Dup ⟨2, by decide⟩),
   opAt 2764 .DIV,
   opAt 2765 (.Swap ⟨1, by decide⟩),
   opAt 2766 .MOD,
   pushAt 2767 2 1600,
   opAt 2768 .MLOAD,
   opAt 2769 .MUL,
   pushAt 2770 2 544,
   opAt 2771 .MLOAD,
   pushAt 2772 2 1536,
   opAt 2773 .MLOAD,
   opAt 2774 (.Swap ⟨0, by decide⟩),
   opAt 2775 .DIV,
   opAt 2776 .ADD,
   pushAt 2777 2 1568,
   opAt 2778 .MLOAD,
   opAt 2779 (.Dup ⟨0, by decide⟩),
   pushAt 2780 2 1632,
   opAt 2781 .MLOAD,
   opAt 2782 (.Dup ⟨4, by decide⟩),
   opAt 2783 .MULMOD,
   opAt 2784 (.Dup ⟨2, by decide⟩),
   opAt 2785 .ADDMOD,
   opAt 2786 (.Swap ⟨0, by decide⟩),
   opAt 2787 .SUB,
   pushAt 2788 2 1664,
   opAt 2789 .MLOAD,
   opAt 2790 .MUL,
   opAt 2791 (.Dup ⟨0, by decide⟩),
   pushAt 2792 0 0,
   opAt 2793 .MLOAD,
   opAt 2794 .MUL,
   pushAt 2795 2 544,
   opAt 2796 .MLOAD,
   opAt 2797 .SUB,
   pushAt 2798 1 32,
   opAt 2799 .MLOAD,
   pushAt 2800 1 128,
   opAt 2801 .SHR,
   opAt 2802 (.Dup ⟨2, by decide⟩),
   pushAt 2803 1 128,
   opAt 2804 .SHR,
   opAt 2805 .MUL,
   opAt 2806 .GT,
   opAt 2807 (.Swap ⟨0, by decide⟩),
   opAt 2808 .SUB,
   opAt 2809 (.Swap ⟨0, by decide⟩),
   pushAt 2810 2 1568,
   opAt 2811 .MLOAD,
   opAt 2812 .GT,
   opAt 2813 .ISZERO,
   pushAt 2814 0 0,
   opAt 2815 .SUB,
   opAt 2816 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2817 0 0,
   pushAt 2818 1 31,
   opAt 2819 .NOT,
   pushAt 2820 2 5344,
   opAt 2821 .MLOAD,
   pushAt 2822 2 5312,
   opAt 2823 .MLOAD,
   pushAt 2824 2 1280,
   opAt 2825 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2829 .JUMPDEST,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 .MLOAD,
   pushAt 2832 0 0,
   opAt 2833 .NOT,
   opAt 2834 (.Dup ⟨6, by decide⟩),
   opAt 2835 (.Dup ⟨2, by decide⟩),
   opAt 2836 .MUL,
   opAt 2837 (.Swap ⟨1, by decide⟩),
   opAt 2838 (.Dup ⟨7, by decide⟩),
   opAt 2839 .MULMOD,
   opAt 2840 (.Dup ⟨1, by decide⟩),
   opAt 2841 (.Dup ⟨1, by decide⟩),
   opAt 2842 .LT,
   opAt 2843 .SUB,
   opAt 2844 (.Dup ⟨5, by decide⟩),
   opAt 2845 (.Dup ⟨2, by decide⟩),
   opAt 2846 .ADD,
   opAt 2847 (.Dup ⟨0, by decide⟩),
   opAt 2848 (.Swap ⟨6, by decide⟩),
   opAt 2849 .GT,
   opAt 2850 .SUB,
   opAt 2851 .SUB,
   opAt 2852 (.Dup ⟨4, by decide⟩),
   opAt 2853 (.Dup ⟨3, by decide⟩),
   opAt 2854 .MLOAD,
   opAt 2855 .ADD,
   opAt 2856 (.Dup ⟨0, by decide⟩),
   opAt 2857 (.Swap ⟨5, by decide⟩),
   opAt 2858 .GT,
   opAt 2859 .ADD,
   opAt 2860 (.Swap ⟨3, by decide⟩),
   opAt 2861 (.Dup ⟨2, by decide⟩),
   opAt 2862 (.Dup ⟨4, by decide⟩),
   opAt 2863 .ADD,
   opAt 2864 (.Swap ⟨2, by decide⟩),
   opAt 2865 .MSTORE,
   opAt 2866 (.Dup ⟨2, by decide⟩),
   opAt 2867 .ADD,
   pushAt 2985 2 4128,
   opAt 2986 (.Dup ⟨2, by decide⟩),
   opAt 2987 .GT,
   pushAt 2988 2 3780,
   opAt 2989 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2990 .POP,
   opAt 2991 .POP,
   opAt 2992 .POP,
   pushAt 2993 2 4128,
   opAt 2994 .MLOAD,
   opAt 2995 (.Dup ⟨1, by decide⟩),
   opAt 2996 .ADD,
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 (.Dup ⟨1, by decide⟩),
   opAt 2999 .LT,
   opAt 3000 (.Swap ⟨1, by decide⟩),
   opAt 3001 .POP,
   opAt 3002 (.Dup ⟨2, by decide⟩),
   opAt 3003 (.Dup ⟨1, by decide⟩),
   opAt 3004 .LT,
   opAt 3005 (.Swap ⟨0, by decide⟩),
   opAt 3006 (.Dup ⟨3, by decide⟩),
   opAt 3007 (.Swap ⟨0, by decide⟩),
   opAt 3008 .SUB,
   opAt 3009 (.Dup ⟨0, by decide⟩),
   pushAt 3010 2 4128,
   opAt 3011 .MSTORE,
   opAt 3012 .POP,
   opAt 3013 .GT,
   opAt 3014 (.Swap ⟨0, by decide⟩),
   opAt 3015 .POP,
   opAt 3016 .ISZERO,
   pushAt 3017 2 4047,
   opAt 3018 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3019 .JUMPDEST,
   pushAt 3020 0 0,
   pushAt 3021 2 5344,
   opAt 3022 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3023 .JUMPDEST,
   opAt 3024 (.Dup ⟨0, by decide⟩),
   opAt 3025 .MLOAD,
   opAt 3026 (.Dup ⟨1, by decide⟩),
   pushAt 3027 2 4160,
   opAt 3028 (.Swap ⟨0, by decide⟩),
   opAt 3029 .SUB,
   opAt 3030 .MLOAD,
   opAt 3031 (.Dup ⟨1, by decide⟩),
   opAt 3032 .ADD,
   opAt 3033 (.Dup ⟨0, by decide⟩),
   opAt 3034 (.Dup ⟨2, by decide⟩),
   opAt 3035 .GT,
   opAt 3036 (.Swap ⟨1, by decide⟩),
   opAt 3037 .POP,
   opAt 3038 (.Dup ⟨3, by decide⟩),
   opAt 3039 .ADD,
   opAt 3040 (.Dup ⟨0, by decide⟩),
   opAt 3041 (.Dup ⟨4, by decide⟩),
   opAt 3042 .GT,
   opAt 3043 (.Swap ⟨3, by decide⟩),
   opAt 3044 .POP,
   opAt 3045 (.Dup ⟨2, by decide⟩),
   opAt 3046 .MSTORE,
   opAt 3047 (.Swap ⟨0, by decide⟩),
   opAt 3048 (.Swap ⟨1, by decide⟩),
   opAt 3049 .OR,
   opAt 3050 (.Swap ⟨0, by decide⟩),
   pushAt 3051 1 31,
   opAt 3052 .NOT,
   opAt 3053 .ADD,
   pushAt 3054 2 4159,
   opAt 3055 (.Dup ⟨1, by decide⟩),
   opAt 3056 .GT,
   pushAt 3057 2 3986,
   opAt 3058 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3059 .POP,
   pushAt 3060 2 4128,
   opAt 3061 .MLOAD,
   opAt 3062 (.Dup ⟨1, by decide⟩),
   opAt 3063 .ADD,
   opAt 3064 (.Dup ⟨0, by decide⟩),
   pushAt 3065 2 4128,
   opAt 3066 .MSTORE,
   opAt 3067 .LT,
   opAt 3068 .ISZERO,
   pushAt 3069 2 3980,
   opAt 3070 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3071 .JUMPDEST,
   pushAt 3072 2 4128,
   opAt 3073 .MLOAD,
   opAt 3074 .ISZERO,
   pushAt 3075 2 4115,
   opAt 3076 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3077 0 0,
   pushAt 3078 2 5344,
   opAt 3079 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3080 .JUMPDEST,
   opAt 3081 (.Dup ⟨0, by decide⟩),
   opAt 3082 .MLOAD,
   pushAt 3083 2 4160,
   opAt 3084 (.Dup ⟨2, by decide⟩),
   opAt 3085 .SUB,
   opAt 3086 .MLOAD,
   opAt 3087 (.Dup ⟨1, by decide⟩),
   opAt 3088 (.Dup ⟨1, by decide⟩),
   opAt 3089 .GT,
   opAt 3090 (.Swap ⟨1, by decide⟩),
   opAt 3091 .SUB,
   opAt 3092 (.Dup ⟨3, by decide⟩),
   opAt 3093 (.Dup ⟨1, by decide⟩),
   opAt 3094 .LT,
   opAt 3095 (.Swap ⟨0, by decide⟩),
   opAt 3096 (.Dup ⟨4, by decide⟩),
   opAt 3097 (.Swap ⟨0, by decide⟩),
   opAt 3098 .SUB,
   opAt 3099 (.Dup ⟨3, by decide⟩),
   opAt 3100 .MSTORE,
   opAt 3101 .OR,
   opAt 3102 (.Swap ⟨1, by decide⟩),
   opAt 3103 .POP,
   pushAt 3104 1 31,
   opAt 3105 .NOT,
   opAt 3106 .ADD,
   pushAt 3107 2 4159,
   opAt 3108 (.Dup ⟨1, by decide⟩),
   opAt 3109 .GT,
   pushAt 3110 2 4062,
   opAt 3111 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3112 .POP,
   pushAt 3113 2 4128,
   opAt 3114 .MLOAD,
   opAt 3115 .SUB,
   pushAt 3116 2 4128,
   opAt 3117 .MSTORE,
   pushAt 3118 2 4047,
   opAt 3119 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3120 .JUMPDEST,
   pushAt 3121 2 4126,
   pushAt 3122 2 512,
   pushAt 3123 2 4885,
   opAt 3124 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3125 .JUMPDEST,
   pushAt 3126 0 0,
   opAt 3127 .NOT,
   opAt 3128 .ADD,
   pushAt 3129 2 3656,
   opAt 3130 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3131 .JUMPDEST,
   opAt 3132 .POP,
   pushAt 3133 2 5248,
   opAt 3134 .MLOAD,
   pushAt 3135 2 1280,
   pushAt 3136 2 1024,
   opAt 3137 .MCOPY,
   pushAt 3138 2 3275,
   opAt 3139 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3433 = true :=
  Artifact.isValidJumpDest_index 2583 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3477 = true :=
  Artifact.isValidJumpDest_index 2610 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3494 = true :=
  Artifact.isValidJumpDest_index 2618 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3501 = true :=
  Artifact.isValidJumpDest_index 2622 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3532 = true :=
  Artifact.isValidJumpDest_index 2646 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3656 = true :=
  Artifact.isValidJumpDest_index 2745 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3780 = true :=
  Artifact.isValidJumpDest_index 2829 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3980 = true :=
  Artifact.isValidJumpDest_index 3019 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3986 = true :=
  Artifact.isValidJumpDest_index 3023 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4047 = true :=
  Artifact.isValidJumpDest_index 3071 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4062 = true :=
  Artifact.isValidJumpDest_index 3080 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4115 = true :=
  Artifact.isValidJumpDest_index 3120 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4126 = true :=
  Artifact.isValidJumpDest_index 3125 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4134 = true :=
  Artifact.isValidJumpDest_index 3131 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
