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
  [opAt 2556 .JUMPDEST,
   opAt 2557 (.Dup ⟨0, by decide⟩),
   opAt 2558 (.Dup ⟨3, by decide⟩),
   opAt 2559 .EQ,
   pushAt 2560 0 0,
   opAt 2561 .MLOAD,
   pushAt 2562 1 255,
   opAt 2563 .SHR,
   opAt 2564 .AND,
   opAt 2565 .ISZERO,
   pushAt 2566 2 3381,
   opAt 2567 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2568 (.Dup ⟨0, by decide⟩),
   pushAt 2569 1 96,
   pushAt 2570 2 1024,
   opAt 2571 .CALLDATACOPY,
   opAt 2572 (.Dup ⟨0, by decide⟩),
   pushAt 2573 1 96,
   pushAt 2574 2 8256,
   opAt 2575 .CALLDATACOPY,
   pushAt 2576 0 0,
   pushAt 2577 2 8224,
   opAt 2578 .MSTORE,
   pushAt 2579 2 3398,
   pushAt 2580 2 2048,
   pushAt 2581 2 4792,
   opAt 2582 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .JUMPDEST,
   pushAt 2584 1 1,
   pushAt 2585 2 4096,
   opAt 2586 .MSTORE,
   pushAt 2587 2 1348,
   pushAt 2588 2 4096,
   pushAt 2589 2 2129,
   opAt 2590 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2591 .JUMPDEST,
   pushAt 2592 1 1,
   pushAt 2593 2 9408,
   opAt 2594 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2595 .JUMPDEST,
   opAt 2596 (.Dup ⟨0, by decide⟩),
   opAt 2597 .MLOAD,
   opAt 2598 .NOT,
   opAt 2599 (.Dup ⟨2, by decide⟩),
   opAt 2600 .ADD,
   opAt 2601 (.Dup ⟨2, by decide⟩),
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 .LT,
   opAt 2604 (.Swap ⟨2, by decide⟩),
   opAt 2605 .POP,
   opAt 2606 (.Dup ⟨1, by decide⟩),
   pushAt 2607 2 5120,
   opAt 2608 .ADD,
   opAt 2609 .MSTORE,
   opAt 2610 (.Dup ⟨0, by decide⟩),
   opAt 2611 .ISZERO,
   pushAt 2612 2 3436,
   opAt 2613 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2614 1 31,
   opAt 2615 .NOT,
   opAt 2616 .ADD,
   pushAt 2617 2 3405,
   opAt 2618 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2619 .JUMPDEST,
   opAt 2620 .POP,
   opAt 2621 .POP,
   pushAt 2622 0 0,
   opAt 2623 .MLOAD,
   opAt 2624 (.Dup ⟨0, by decide⟩),
   pushAt 2625 0 0,
   opAt 2626 .SUB,
   opAt 2627 (.Dup ⟨1, by decide⟩),
   opAt 2628 .AND,
   opAt 2629 (.Dup ⟨0, by decide⟩),
   pushAt 2630 2 6144,
   opAt 2631 .MSTORE,
   opAt 2632 (.Dup ⟨0, by decide⟩),
   opAt 2633 (.Dup ⟨2, by decide⟩),
   opAt 2634 .DIV,
   opAt 2635 (.Dup ⟨0, by decide⟩),
   pushAt 2636 2 6176,
   opAt 2637 .MSTORE,
   opAt 2638 (.Dup ⟨1, by decide⟩),
   pushAt 2639 0 0,
   opAt 2640 .SUB,
   opAt 2641 (.Dup ⟨2, by decide⟩),
   opAt 2642 (.Swap ⟨0, by decide⟩),
   opAt 2643 .DIV,
   pushAt 2644 1 1,
   opAt 2645 .ADD,
   pushAt 2646 2 6208,
   opAt 2647 .MSTORE,
   opAt 2648 (.Dup ⟨0, by decide⟩),
   pushAt 2649 0 0,
   opAt 2650 .SUB,
   opAt 2651 (.Dup ⟨1, by decide⟩),
   opAt 2652 (.Swap ⟨0, by decide⟩),
   opAt 2653 .MOD,
   pushAt 2654 2 6240,
   opAt 2655 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2656 (.Dup ⟨0, by decide⟩),
   pushAt 2657 1 2,
   opAt 2658 .SUB,
   opAt 2659 (.Dup ⟨0, by decide⟩),
   opAt 2660 (.Dup ⟨2, by decide⟩),
   opAt 2661 .MUL,
   pushAt 2662 1 2,
   opAt 2663 .SUB,
   opAt 2664 .MUL,
   opAt 2665 (.Dup ⟨0, by decide⟩),
   opAt 2666 (.Dup ⟨2, by decide⟩),
   opAt 2667 .MUL,
   pushAt 2668 1 2,
   opAt 2669 .SUB,
   opAt 2670 .MUL,
   opAt 2671 (.Dup ⟨0, by decide⟩),
   opAt 2672 (.Dup ⟨2, by decide⟩),
   opAt 2673 .MUL,
   pushAt 2674 1 2,
   opAt 2675 .SUB,
   opAt 2676 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2677 (.Dup ⟨0, by decide⟩),
   opAt 2678 (.Dup ⟨2, by decide⟩),
   opAt 2679 .MUL,
   pushAt 2680 1 2,
   opAt 2681 .SUB,
   opAt 2682 .MUL,
   opAt 2683 (.Dup ⟨0, by decide⟩),
   opAt 2684 (.Dup ⟨2, by decide⟩),
   opAt 2685 .MUL,
   pushAt 2686 1 2,
   opAt 2687 .SUB,
   opAt 2688 .MUL,
   opAt 2689 (.Dup ⟨0, by decide⟩),
   opAt 2690 (.Dup ⟨2, by decide⟩),
   opAt 2691 .MUL,
   pushAt 2692 1 2,
   opAt 2693 .SUB,
   opAt 2694 .MUL,
   opAt 2695 (.Dup ⟨0, by decide⟩),
   opAt 2696 (.Dup ⟨2, by decide⟩),
   opAt 2697 .MUL,
   pushAt 2698 1 2,
   opAt 2699 .SUB,
   opAt 2700 .MUL,
   pushAt 2701 2 6272,
   opAt 2702 .MSTORE,
   opAt 2703 .POP,
   opAt 2704 .POP,
   opAt 2705 .POP,
   opAt 2706 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2718 .JUMPDEST,
   opAt 2719 (.Dup ⟨0, by decide⟩),
   opAt 2720 .ISZERO,
   pushAt 2721 2 4038,
   opAt 2722 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2723 (.Dup ⟨1, by decide⟩),
   pushAt 2724 2 2048,
   pushAt 2725 2 8224,
   opAt 2726 .MCOPY,
   pushAt 2727 0 0,
   pushAt 2728 2 9440,
   opAt 2729 .MLOAD,
   opAt 2730 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2731 2 2048,
   opAt 2732 .MLOAD,
   pushAt 2733 2 6144,
   opAt 2734 .MLOAD,
   opAt 2735 (.Dup ⟨0, by decide⟩),
   opAt 2736 (.Dup ⟨2, by decide⟩),
   opAt 2737 .DIV,
   opAt 2738 (.Swap ⟨1, by decide⟩),
   opAt 2739 .MOD,
   pushAt 2740 2 6208,
   opAt 2741 .MLOAD,
   opAt 2742 .MUL,
   pushAt 2743 2 2080,
   opAt 2744 .MLOAD,
   pushAt 2745 2 6144,
   opAt 2746 .MLOAD,
   opAt 2747 (.Swap ⟨0, by decide⟩),
   opAt 2748 .DIV,
   opAt 2749 .ADD,
   pushAt 2750 2 6176,
   opAt 2751 .MLOAD,
   opAt 2752 (.Dup ⟨0, by decide⟩),
   pushAt 2753 2 6240,
   opAt 2754 .MLOAD,
   opAt 2755 (.Dup ⟨4, by decide⟩),
   opAt 2756 .MULMOD,
   opAt 2757 (.Dup ⟨2, by decide⟩),
   opAt 2758 .ADDMOD,
   opAt 2759 (.Swap ⟨0, by decide⟩),
   opAt 2760 .SUB,
   pushAt 2761 2 6272,
   opAt 2762 .MLOAD,
   opAt 2763 .MUL,
   opAt 2764 (.Dup ⟨0, by decide⟩),
   pushAt 2765 0 0,
   opAt 2766 .MLOAD,
   opAt 2767 .MUL,
   pushAt 2768 2 2080,
   opAt 2769 .MLOAD,
   opAt 2770 .SUB,
   pushAt 2771 1 32,
   opAt 2772 .MLOAD,
   pushAt 2773 1 128,
   opAt 2774 .SHR,
   opAt 2775 (.Dup ⟨2, by decide⟩),
   pushAt 2776 1 128,
   opAt 2777 .SHR,
   opAt 2778 .MUL,
   opAt 2779 .GT,
   opAt 2780 (.Swap ⟨0, by decide⟩),
   opAt 2781 .SUB,
   opAt 2782 (.Swap ⟨0, by decide⟩),
   pushAt 2783 2 6176,
   opAt 2784 .MLOAD,
   opAt 2785 .GT,
   opAt 2786 .ISZERO,
   pushAt 2787 0 0,
   opAt 2788 .SUB,
   opAt 2789 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2790 0 0,
   pushAt 2791 1 31,
   opAt 2792 .NOT,
   pushAt 2793 2 9440,
   opAt 2794 .MLOAD,
   pushAt 2795 2 9408,
   opAt 2796 .MLOAD,
   pushAt 2797 2 5120,
   opAt 2798 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2802 .JUMPDEST,
   opAt 2803 (.Dup ⟨0, by decide⟩),
   opAt 2804 .MLOAD,
   pushAt 2805 0 0,
   opAt 2806 .NOT,
   opAt 2807 (.Dup ⟨6, by decide⟩),
   opAt 2808 (.Dup ⟨2, by decide⟩),
   opAt 2809 .MUL,
   opAt 2810 (.Swap ⟨1, by decide⟩),
   opAt 2811 (.Dup ⟨7, by decide⟩),
   opAt 2812 .MULMOD,
   opAt 2813 (.Dup ⟨1, by decide⟩),
   opAt 2814 (.Dup ⟨1, by decide⟩),
   opAt 2815 .LT,
   opAt 2816 .SUB,
   opAt 2817 (.Dup ⟨5, by decide⟩),
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .ADD,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   opAt 2821 (.Swap ⟨6, by decide⟩),
   opAt 2822 .GT,
   opAt 2823 .SUB,
   opAt 2824 .SUB,
   opAt 2825 (.Dup ⟨4, by decide⟩),
   opAt 2826 (.Dup ⟨3, by decide⟩),
   opAt 2827 .MLOAD,
   opAt 2828 .ADD,
   opAt 2829 (.Dup ⟨0, by decide⟩),
   opAt 2830 (.Swap ⟨5, by decide⟩),
   opAt 2831 .GT,
   opAt 2832 .ADD,
   opAt 2833 (.Swap ⟨3, by decide⟩),
   opAt 2834 (.Dup ⟨2, by decide⟩),
   opAt 2835 (.Dup ⟨4, by decide⟩),
   opAt 2836 .ADD,
   opAt 2837 (.Swap ⟨2, by decide⟩),
   opAt 2838 .MSTORE,
   opAt 2839 (.Dup ⟨2, by decide⟩),
   opAt 2840 .ADD,
   pushAt 2958 2 8224,
   opAt 2959 (.Dup ⟨2, by decide⟩),
   opAt 2960 .GT,
   pushAt 2961 2 3684,
   opAt 2962 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2963 .POP,
   opAt 2964 .POP,
   opAt 2965 .POP,
   pushAt 2966 2 8224,
   opAt 2967 .MLOAD,
   opAt 2968 (.Dup ⟨1, by decide⟩),
   opAt 2969 .ADD,
   opAt 2970 (.Dup ⟨1, by decide⟩),
   opAt 2971 (.Dup ⟨1, by decide⟩),
   opAt 2972 .LT,
   opAt 2973 (.Swap ⟨1, by decide⟩),
   opAt 2974 .POP,
   opAt 2975 (.Dup ⟨2, by decide⟩),
   opAt 2976 (.Dup ⟨1, by decide⟩),
   opAt 2977 .LT,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 (.Dup ⟨3, by decide⟩),
   opAt 2980 (.Swap ⟨0, by decide⟩),
   opAt 2981 .SUB,
   opAt 2982 (.Dup ⟨0, by decide⟩),
   pushAt 2983 2 8224,
   opAt 2984 .MSTORE,
   opAt 2985 .POP,
   opAt 2986 .GT,
   opAt 2987 (.Swap ⟨0, by decide⟩),
   opAt 2988 .POP,
   opAt 2989 .ISZERO,
   pushAt 2990 2 3951,
   opAt 2991 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2992 .JUMPDEST,
   pushAt 2993 0 0,
   pushAt 2994 2 9440,
   opAt 2995 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2996 .JUMPDEST,
   opAt 2997 (.Dup ⟨0, by decide⟩),
   opAt 2998 .MLOAD,
   opAt 2999 (.Dup ⟨1, by decide⟩),
   pushAt 3000 2 8256,
   opAt 3001 (.Swap ⟨0, by decide⟩),
   opAt 3002 .SUB,
   opAt 3003 .MLOAD,
   opAt 3004 (.Dup ⟨1, by decide⟩),
   opAt 3005 .ADD,
   opAt 3006 (.Dup ⟨0, by decide⟩),
   opAt 3007 (.Dup ⟨2, by decide⟩),
   opAt 3008 .GT,
   opAt 3009 (.Swap ⟨1, by decide⟩),
   opAt 3010 .POP,
   opAt 3011 (.Dup ⟨3, by decide⟩),
   opAt 3012 .ADD,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 (.Dup ⟨4, by decide⟩),
   opAt 3015 .GT,
   opAt 3016 (.Swap ⟨3, by decide⟩),
   opAt 3017 .POP,
   opAt 3018 (.Dup ⟨2, by decide⟩),
   opAt 3019 .MSTORE,
   opAt 3020 (.Swap ⟨0, by decide⟩),
   opAt 3021 (.Swap ⟨1, by decide⟩),
   opAt 3022 .OR,
   opAt 3023 (.Swap ⟨0, by decide⟩),
   pushAt 3024 1 31,
   opAt 3025 .NOT,
   opAt 3026 .ADD,
   pushAt 3027 2 8255,
   opAt 3028 (.Dup ⟨1, by decide⟩),
   opAt 3029 .GT,
   pushAt 3030 2 3890,
   opAt 3031 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3032 .POP,
   pushAt 3033 2 8224,
   opAt 3034 .MLOAD,
   opAt 3035 (.Dup ⟨1, by decide⟩),
   opAt 3036 .ADD,
   opAt 3037 (.Dup ⟨0, by decide⟩),
   pushAt 3038 2 8224,
   opAt 3039 .MSTORE,
   opAt 3040 .LT,
   opAt 3041 .ISZERO,
   pushAt 3042 2 3884,
   opAt 3043 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3044 .JUMPDEST,
   pushAt 3045 2 8224,
   opAt 3046 .MLOAD,
   opAt 3047 .ISZERO,
   pushAt 3048 2 4019,
   opAt 3049 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3050 0 0,
   pushAt 3051 2 9440,
   opAt 3052 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3053 .JUMPDEST,
   opAt 3054 (.Dup ⟨0, by decide⟩),
   opAt 3055 .MLOAD,
   pushAt 3056 2 8256,
   opAt 3057 (.Dup ⟨2, by decide⟩),
   opAt 3058 .SUB,
   opAt 3059 .MLOAD,
   opAt 3060 (.Dup ⟨1, by decide⟩),
   opAt 3061 (.Dup ⟨1, by decide⟩),
   opAt 3062 .GT,
   opAt 3063 (.Swap ⟨1, by decide⟩),
   opAt 3064 .SUB,
   opAt 3065 (.Dup ⟨3, by decide⟩),
   opAt 3066 (.Dup ⟨1, by decide⟩),
   opAt 3067 .LT,
   opAt 3068 (.Swap ⟨0, by decide⟩),
   opAt 3069 (.Dup ⟨4, by decide⟩),
   opAt 3070 (.Swap ⟨0, by decide⟩),
   opAt 3071 .SUB,
   opAt 3072 (.Dup ⟨3, by decide⟩),
   opAt 3073 .MSTORE,
   opAt 3074 .OR,
   opAt 3075 (.Swap ⟨1, by decide⟩),
   opAt 3076 .POP,
   pushAt 3077 1 31,
   opAt 3078 .NOT,
   opAt 3079 .ADD,
   pushAt 3080 2 8255,
   opAt 3081 (.Dup ⟨1, by decide⟩),
   opAt 3082 .GT,
   pushAt 3083 2 3966,
   opAt 3084 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3085 .POP,
   pushAt 3086 2 8224,
   opAt 3087 .MLOAD,
   opAt 3088 .SUB,
   pushAt 3089 2 8224,
   opAt 3090 .MSTORE,
   pushAt 3091 2 3951,
   opAt 3092 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3093 .JUMPDEST,
   pushAt 3094 2 4030,
   pushAt 3095 2 2048,
   pushAt 3096 2 4792,
   opAt 3097 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3098 .JUMPDEST,
   pushAt 3099 0 0,
   opAt 3100 .NOT,
   opAt 3101 .ADD,
   pushAt 3102 2 3560,
   opAt 3103 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3104 .JUMPDEST,
   opAt 3105 .POP,
   pushAt 3106 2 9344,
   opAt 3107 .MLOAD,
   pushAt 3108 2 5120,
   pushAt 3109 2 4096,
   opAt 3110 .MCOPY,
   pushAt 3111 2 3179,
   opAt 3112 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3337 = true :=
  Artifact.isValidJumpDest_index 2556 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3381 = true :=
  Artifact.isValidJumpDest_index 2583 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3398 = true :=
  Artifact.isValidJumpDest_index 2591 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3405 = true :=
  Artifact.isValidJumpDest_index 2595 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3436 = true :=
  Artifact.isValidJumpDest_index 2619 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3560 = true :=
  Artifact.isValidJumpDest_index 2718 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3684 = true :=
  Artifact.isValidJumpDest_index 2802 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3884 = true :=
  Artifact.isValidJumpDest_index 2992 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3890 = true :=
  Artifact.isValidJumpDest_index 2996 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3951 = true :=
  Artifact.isValidJumpDest_index 3044 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3966 = true :=
  Artifact.isValidJumpDest_index 3053 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4019 = true :=
  Artifact.isValidJumpDest_index 3093 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4030 = true :=
  Artifact.isValidJumpDest_index 3098 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4038 = true :=
  Artifact.isValidJumpDest_index 3104 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
