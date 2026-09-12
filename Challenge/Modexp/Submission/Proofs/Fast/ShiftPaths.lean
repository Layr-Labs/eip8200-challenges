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
  [opAt 2577 .JUMPDEST,
   opAt 2578 (.Dup ⟨0, by decide⟩),
   opAt 2579 (.Dup ⟨3, by decide⟩),
   opAt 2580 .EQ,
   pushAt 2581 0 0,
   opAt 2582 .MLOAD,
   pushAt 2583 1 255,
   opAt 2584 .SHR,
   opAt 2585 .AND,
   opAt 2586 .ISZERO,
   pushAt 2587 2 3467,
   opAt 2588 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2589 (.Dup ⟨0, by decide⟩),
   pushAt 2590 1 96,
   pushAt 2591 2 256,
   opAt 2592 .CALLDATACOPY,
   opAt 2593 (.Dup ⟨0, by decide⟩),
   pushAt 2594 1 96,
   pushAt 2595 2 4160,
   opAt 2596 .CALLDATACOPY,
   pushAt 2597 0 0,
   pushAt 2598 2 4128,
   opAt 2599 .MSTORE,
   pushAt 2600 2 3484,
   pushAt 2601 2 512,
   pushAt 2602 2 4875,
   opAt 2603 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2604 .JUMPDEST,
   pushAt 2605 1 1,
   pushAt 2606 2 1024,
   opAt 2607 .MSTORE,
   pushAt 2608 2 1430,
   pushAt 2609 2 1024,
   pushAt 2610 2 2206,
   opAt 2611 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2612 .JUMPDEST,
   pushAt 2613 1 1,
   pushAt 2614 2 5312,
   opAt 2615 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2616 .JUMPDEST,
   opAt 2617 (.Dup ⟨0, by decide⟩),
   opAt 2618 .MLOAD,
   opAt 2619 .NOT,
   opAt 2620 (.Dup ⟨2, by decide⟩),
   opAt 2621 .ADD,
   opAt 2622 (.Dup ⟨2, by decide⟩),
   opAt 2623 (.Dup ⟨1, by decide⟩),
   opAt 2624 .LT,
   opAt 2625 (.Swap ⟨2, by decide⟩),
   opAt 2626 .POP,
   opAt 2627 (.Dup ⟨1, by decide⟩),
   pushAt 2628 2 1280,
   opAt 2629 .ADD,
   opAt 2630 .MSTORE,
   opAt 2631 (.Dup ⟨0, by decide⟩),
   opAt 2632 .ISZERO,
   pushAt 2633 2 3522,
   opAt 2634 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2635 1 31,
   opAt 2636 .NOT,
   opAt 2637 .ADD,
   pushAt 2638 2 3491,
   opAt 2639 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2640 .JUMPDEST,
   opAt 2641 .POP,
   opAt 2642 .POP,
   pushAt 2643 0 0,
   opAt 2644 .MLOAD,
   opAt 2645 (.Dup ⟨0, by decide⟩),
   pushAt 2646 0 0,
   opAt 2647 .SUB,
   opAt 2648 (.Dup ⟨1, by decide⟩),
   opAt 2649 .AND,
   opAt 2650 (.Dup ⟨0, by decide⟩),
   pushAt 2651 2 1536,
   opAt 2652 .MSTORE,
   opAt 2653 (.Dup ⟨0, by decide⟩),
   opAt 2654 (.Dup ⟨2, by decide⟩),
   opAt 2655 .DIV,
   opAt 2656 (.Dup ⟨0, by decide⟩),
   pushAt 2657 2 1568,
   opAt 2658 .MSTORE,
   opAt 2659 (.Dup ⟨1, by decide⟩),
   pushAt 2660 0 0,
   opAt 2661 .SUB,
   opAt 2662 (.Dup ⟨2, by decide⟩),
   opAt 2663 (.Swap ⟨0, by decide⟩),
   opAt 2664 .DIV,
   pushAt 2665 1 1,
   opAt 2666 .ADD,
   pushAt 2667 2 1600,
   opAt 2668 .MSTORE,
   opAt 2669 (.Dup ⟨0, by decide⟩),
   pushAt 2670 0 0,
   opAt 2671 .SUB,
   opAt 2672 (.Dup ⟨1, by decide⟩),
   opAt 2673 (.Swap ⟨0, by decide⟩),
   opAt 2674 .MOD,
   pushAt 2675 2 1632,
   opAt 2676 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2677 (.Dup ⟨0, by decide⟩),
   pushAt 2678 1 2,
   opAt 2679 .SUB,
   opAt 2680 (.Dup ⟨0, by decide⟩),
   opAt 2681 (.Dup ⟨2, by decide⟩),
   opAt 2682 .MUL,
   pushAt 2683 1 2,
   opAt 2684 .SUB,
   opAt 2685 .MUL,
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
   opAt 2697 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2698 (.Dup ⟨0, by decide⟩),
   opAt 2699 (.Dup ⟨2, by decide⟩),
   opAt 2700 .MUL,
   pushAt 2701 1 2,
   opAt 2702 .SUB,
   opAt 2703 .MUL,
   opAt 2704 (.Dup ⟨0, by decide⟩),
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
   pushAt 2722 2 1664,
   opAt 2723 .MSTORE,
   opAt 2724 .POP,
   opAt 2725 .POP,
   opAt 2726 .POP,
   opAt 2727 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2739 .JUMPDEST,
   opAt 2740 (.Dup ⟨0, by decide⟩),
   opAt 2741 .ISZERO,
   pushAt 2742 2 4124,
   opAt 2743 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2744 (.Dup ⟨1, by decide⟩),
   pushAt 2745 2 512,
   pushAt 2746 2 4128,
   opAt 2747 .MCOPY,
   pushAt 2748 0 0,
   pushAt 2749 2 5344,
   opAt 2750 .MLOAD,
   opAt 2751 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2752 2 512,
   opAt 2753 .MLOAD,
   pushAt 2754 2 1536,
   opAt 2755 .MLOAD,
   opAt 2756 (.Dup ⟨0, by decide⟩),
   opAt 2757 (.Dup ⟨2, by decide⟩),
   opAt 2758 .DIV,
   opAt 2759 (.Swap ⟨1, by decide⟩),
   opAt 2760 .MOD,
   pushAt 2761 2 1600,
   opAt 2762 .MLOAD,
   opAt 2763 .MUL,
   pushAt 2764 2 544,
   opAt 2765 .MLOAD,
   pushAt 2766 2 1536,
   opAt 2767 .MLOAD,
   opAt 2768 (.Swap ⟨0, by decide⟩),
   opAt 2769 .DIV,
   opAt 2770 .ADD,
   pushAt 2771 2 1568,
   opAt 2772 .MLOAD,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   pushAt 2774 2 1632,
   opAt 2775 .MLOAD,
   opAt 2776 (.Dup ⟨4, by decide⟩),
   opAt 2777 .MULMOD,
   opAt 2778 (.Dup ⟨2, by decide⟩),
   opAt 2779 .ADDMOD,
   opAt 2780 (.Swap ⟨0, by decide⟩),
   opAt 2781 .SUB,
   pushAt 2782 2 1664,
   opAt 2783 .MLOAD,
   opAt 2784 .MUL,
   opAt 2785 (.Dup ⟨0, by decide⟩),
   pushAt 2786 0 0,
   opAt 2787 .MLOAD,
   opAt 2788 .MUL,
   pushAt 2789 2 544,
   opAt 2790 .MLOAD,
   opAt 2791 .SUB,
   pushAt 2792 1 32,
   opAt 2793 .MLOAD,
   pushAt 2794 1 128,
   opAt 2795 .SHR,
   opAt 2796 (.Dup ⟨2, by decide⟩),
   pushAt 2797 1 128,
   opAt 2798 .SHR,
   opAt 2799 .MUL,
   opAt 2800 .GT,
   opAt 2801 (.Swap ⟨0, by decide⟩),
   opAt 2802 .SUB,
   opAt 2803 (.Swap ⟨0, by decide⟩),
   pushAt 2804 2 1568,
   opAt 2805 .MLOAD,
   opAt 2806 .GT,
   opAt 2807 .ISZERO,
   pushAt 2808 0 0,
   opAt 2809 .SUB,
   opAt 2810 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2811 0 0,
   pushAt 2812 1 31,
   opAt 2813 .NOT,
   pushAt 2814 2 5344,
   opAt 2815 .MLOAD,
   pushAt 2816 2 5312,
   opAt 2817 .MLOAD,
   pushAt 2818 2 1280,
   opAt 2819 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2823 .JUMPDEST,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   opAt 2825 .MLOAD,
   pushAt 2826 0 0,
   opAt 2827 .NOT,
   opAt 2828 (.Dup ⟨6, by decide⟩),
   opAt 2829 (.Dup ⟨2, by decide⟩),
   opAt 2830 .MUL,
   opAt 2831 (.Swap ⟨1, by decide⟩),
   opAt 2832 (.Dup ⟨7, by decide⟩),
   opAt 2833 .MULMOD,
   opAt 2834 (.Dup ⟨1, by decide⟩),
   opAt 2835 (.Dup ⟨1, by decide⟩),
   opAt 2836 .LT,
   opAt 2837 .SUB,
   opAt 2838 (.Dup ⟨5, by decide⟩),
   opAt 2839 (.Dup ⟨2, by decide⟩),
   opAt 2840 .ADD,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   opAt 2842 (.Swap ⟨6, by decide⟩),
   opAt 2843 .GT,
   opAt 2844 .SUB,
   opAt 2845 .SUB,
   opAt 2846 (.Dup ⟨4, by decide⟩),
   opAt 2847 (.Dup ⟨3, by decide⟩),
   opAt 2848 .MLOAD,
   opAt 2849 .ADD,
   opAt 2850 (.Dup ⟨0, by decide⟩),
   opAt 2851 (.Swap ⟨5, by decide⟩),
   opAt 2852 .GT,
   opAt 2853 .ADD,
   opAt 2854 (.Swap ⟨3, by decide⟩),
   opAt 2855 (.Dup ⟨2, by decide⟩),
   opAt 2856 (.Dup ⟨4, by decide⟩),
   opAt 2857 .ADD,
   opAt 2858 (.Swap ⟨2, by decide⟩),
   opAt 2859 .MSTORE,
   opAt 2860 (.Dup ⟨2, by decide⟩),
   opAt 2861 .ADD,
   pushAt 2979 2 4128,
   opAt 2980 (.Dup ⟨2, by decide⟩),
   opAt 2981 .GT,
   pushAt 2982 2 3770,
   opAt 2983 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2984 .POP,
   opAt 2985 .POP,
   opAt 2986 .POP,
   pushAt 2987 2 4128,
   opAt 2988 .MLOAD,
   opAt 2989 (.Dup ⟨1, by decide⟩),
   opAt 2990 .ADD,
   opAt 2991 (.Dup ⟨1, by decide⟩),
   opAt 2992 (.Dup ⟨1, by decide⟩),
   opAt 2993 .LT,
   opAt 2994 (.Swap ⟨1, by decide⟩),
   opAt 2995 .POP,
   opAt 2996 (.Dup ⟨2, by decide⟩),
   opAt 2997 (.Dup ⟨1, by decide⟩),
   opAt 2998 .LT,
   opAt 2999 (.Swap ⟨0, by decide⟩),
   opAt 3000 (.Dup ⟨3, by decide⟩),
   opAt 3001 (.Swap ⟨0, by decide⟩),
   opAt 3002 .SUB,
   opAt 3003 (.Dup ⟨0, by decide⟩),
   pushAt 3004 2 4128,
   opAt 3005 .MSTORE,
   opAt 3006 .POP,
   opAt 3007 .GT,
   opAt 3008 (.Swap ⟨0, by decide⟩),
   opAt 3009 .POP,
   opAt 3010 .ISZERO,
   pushAt 3011 2 4037,
   opAt 3012 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3013 .JUMPDEST,
   pushAt 3014 0 0,
   pushAt 3015 2 5344,
   opAt 3016 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3017 .JUMPDEST,
   opAt 3018 (.Dup ⟨0, by decide⟩),
   opAt 3019 .MLOAD,
   opAt 3020 (.Dup ⟨1, by decide⟩),
   pushAt 3021 2 4160,
   opAt 3022 (.Swap ⟨0, by decide⟩),
   opAt 3023 .SUB,
   opAt 3024 .MLOAD,
   opAt 3025 (.Dup ⟨1, by decide⟩),
   opAt 3026 .ADD,
   opAt 3027 (.Dup ⟨0, by decide⟩),
   opAt 3028 (.Dup ⟨2, by decide⟩),
   opAt 3029 .GT,
   opAt 3030 (.Swap ⟨1, by decide⟩),
   opAt 3031 .POP,
   opAt 3032 (.Dup ⟨3, by decide⟩),
   opAt 3033 .ADD,
   opAt 3034 (.Dup ⟨0, by decide⟩),
   opAt 3035 (.Dup ⟨4, by decide⟩),
   opAt 3036 .GT,
   opAt 3037 (.Swap ⟨3, by decide⟩),
   opAt 3038 .POP,
   opAt 3039 (.Dup ⟨2, by decide⟩),
   opAt 3040 .MSTORE,
   opAt 3041 (.Swap ⟨0, by decide⟩),
   opAt 3042 (.Swap ⟨1, by decide⟩),
   opAt 3043 .OR,
   opAt 3044 (.Swap ⟨0, by decide⟩),
   pushAt 3045 1 31,
   opAt 3046 .NOT,
   opAt 3047 .ADD,
   pushAt 3048 2 4159,
   opAt 3049 (.Dup ⟨1, by decide⟩),
   opAt 3050 .GT,
   pushAt 3051 2 3976,
   opAt 3052 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3053 .POP,
   pushAt 3054 2 4128,
   opAt 3055 .MLOAD,
   opAt 3056 (.Dup ⟨1, by decide⟩),
   opAt 3057 .ADD,
   opAt 3058 (.Dup ⟨0, by decide⟩),
   pushAt 3059 2 4128,
   opAt 3060 .MSTORE,
   opAt 3061 .LT,
   opAt 3062 .ISZERO,
   pushAt 3063 2 3970,
   opAt 3064 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3065 .JUMPDEST,
   pushAt 3066 2 4128,
   opAt 3067 .MLOAD,
   opAt 3068 .ISZERO,
   pushAt 3069 2 4105,
   opAt 3070 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3071 0 0,
   pushAt 3072 2 5344,
   opAt 3073 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3074 .JUMPDEST,
   opAt 3075 (.Dup ⟨0, by decide⟩),
   opAt 3076 .MLOAD,
   pushAt 3077 2 4160,
   opAt 3078 (.Dup ⟨2, by decide⟩),
   opAt 3079 .SUB,
   opAt 3080 .MLOAD,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 (.Dup ⟨1, by decide⟩),
   opAt 3083 .GT,
   opAt 3084 (.Swap ⟨1, by decide⟩),
   opAt 3085 .SUB,
   opAt 3086 (.Dup ⟨3, by decide⟩),
   opAt 3087 (.Dup ⟨1, by decide⟩),
   opAt 3088 .LT,
   opAt 3089 (.Swap ⟨0, by decide⟩),
   opAt 3090 (.Dup ⟨4, by decide⟩),
   opAt 3091 (.Swap ⟨0, by decide⟩),
   opAt 3092 .SUB,
   opAt 3093 (.Dup ⟨3, by decide⟩),
   opAt 3094 .MSTORE,
   opAt 3095 .OR,
   opAt 3096 (.Swap ⟨1, by decide⟩),
   opAt 3097 .POP,
   pushAt 3098 1 31,
   opAt 3099 .NOT,
   opAt 3100 .ADD,
   pushAt 3101 2 4159,
   opAt 3102 (.Dup ⟨1, by decide⟩),
   opAt 3103 .GT,
   pushAt 3104 2 4052,
   opAt 3105 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3106 .POP,
   pushAt 3107 2 4128,
   opAt 3108 .MLOAD,
   opAt 3109 .SUB,
   pushAt 3110 2 4128,
   opAt 3111 .MSTORE,
   pushAt 3112 2 4037,
   opAt 3113 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3114 .JUMPDEST,
   pushAt 3115 2 4116,
   pushAt 3116 2 512,
   pushAt 3117 2 4875,
   opAt 3118 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3119 .JUMPDEST,
   pushAt 3120 0 0,
   opAt 3121 .NOT,
   opAt 3122 .ADD,
   pushAt 3123 2 3646,
   opAt 3124 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3125 .JUMPDEST,
   opAt 3126 .POP,
   pushAt 3127 2 5248,
   opAt 3128 .MLOAD,
   pushAt 3129 2 1280,
   pushAt 3130 2 1024,
   opAt 3131 .MCOPY,
   pushAt 3132 2 3265,
   opAt 3133 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3423 = true :=
  Artifact.isValidJumpDest_index 2577 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3467 = true :=
  Artifact.isValidJumpDest_index 2604 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3484 = true :=
  Artifact.isValidJumpDest_index 2612 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3491 = true :=
  Artifact.isValidJumpDest_index 2616 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3522 = true :=
  Artifact.isValidJumpDest_index 2640 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3646 = true :=
  Artifact.isValidJumpDest_index 2739 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3770 = true :=
  Artifact.isValidJumpDest_index 2823 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 3013 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3976 = true :=
  Artifact.isValidJumpDest_index 3017 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4037 = true :=
  Artifact.isValidJumpDest_index 3065 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4052 = true :=
  Artifact.isValidJumpDest_index 3074 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4105 = true :=
  Artifact.isValidJumpDest_index 3114 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4116 = true :=
  Artifact.isValidJumpDest_index 3119 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4124 = true :=
  Artifact.isValidJumpDest_index 3125 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
