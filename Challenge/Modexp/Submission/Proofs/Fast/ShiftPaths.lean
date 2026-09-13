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
  [opAt 2535 .JUMPDEST,
   opAt 2536 (.Dup ⟨0, by decide⟩),
   opAt 2537 (.Dup ⟨3, by decide⟩),
   opAt 2538 .EQ,
   pushAt 2539 0 0,
   opAt 2540 .MLOAD,
   pushAt 2541 1 255,
   opAt 2542 .SHR,
   opAt 2543 .AND,
   opAt 2544 .ISZERO,
   pushAt 2545 2 3418,
   opAt 2546 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2547 (.Dup ⟨0, by decide⟩),
   pushAt 2548 1 96,
   pushAt 2549 2 256,
   opAt 2550 .CALLDATACOPY,
   opAt 2551 (.Dup ⟨0, by decide⟩),
   pushAt 2552 1 96,
   pushAt 2553 2 2112,
   opAt 2554 .CALLDATACOPY,
   pushAt 2555 0 0,
   pushAt 2556 2 2080,
   opAt 2557 .MSTORE,
   pushAt 2558 2 3435,
   pushAt 2559 2 512,
   pushAt 2560 2 4877,
   opAt 2561 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2562 .JUMPDEST,
   pushAt 2563 1 1,
   pushAt 2564 2 1024,
   opAt 2565 .MSTORE,
   pushAt 2566 2 1430,
   pushAt 2567 2 1024,
   pushAt 2568 2 2208,
   opAt 2569 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2570 .JUMPDEST,
   pushAt 2571 1 1,
   pushAt 2572 2 2752,
   opAt 2573 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2574 .JUMPDEST,
   opAt 2575 (.Dup ⟨0, by decide⟩),
   opAt 2576 .MLOAD,
   opAt 2577 .NOT,
   opAt 2578 (.Dup ⟨2, by decide⟩),
   opAt 2579 .ADD,
   opAt 2580 (.Dup ⟨2, by decide⟩),
   opAt 2581 (.Dup ⟨1, by decide⟩),
   opAt 2582 .LT,
   opAt 2583 (.Swap ⟨2, by decide⟩),
   opAt 2584 .POP,
   opAt 2585 (.Dup ⟨1, by decide⟩),
   pushAt 2586 2 1280,
   opAt 2587 .ADD,
   opAt 2588 .MSTORE,
   opAt 2589 (.Dup ⟨0, by decide⟩),
   opAt 2590 .ISZERO,
   pushAt 2591 2 3473,
   opAt 2592 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2593 1 31,
   opAt 2594 .NOT,
   opAt 2595 .ADD,
   pushAt 2596 2 3442,
   opAt 2597 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2598 .JUMPDEST,
   opAt 2599 .POP,
   opAt 2600 .POP,
   pushAt 2601 0 0,
   opAt 2602 .MLOAD,
   opAt 2603 (.Dup ⟨0, by decide⟩),
   pushAt 2604 0 0,
   opAt 2605 .SUB,
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 .AND,
   opAt 2608 (.Dup ⟨0, by decide⟩),
   pushAt 2609 2 1536,
   opAt 2610 .MSTORE,
   opAt 2611 (.Dup ⟨0, by decide⟩),
   opAt 2612 (.Dup ⟨2, by decide⟩),
   opAt 2613 .DIV,
   opAt 2614 (.Dup ⟨0, by decide⟩),
   pushAt 2615 2 1568,
   opAt 2616 .MSTORE,
   opAt 2617 (.Dup ⟨1, by decide⟩),
   pushAt 2618 0 0,
   opAt 2619 .SUB,
   opAt 2620 (.Dup ⟨2, by decide⟩),
   opAt 2621 (.Swap ⟨0, by decide⟩),
   opAt 2622 .DIV,
   pushAt 2623 1 1,
   opAt 2624 .ADD,
   pushAt 2625 2 1600,
   opAt 2626 .MSTORE,
   opAt 2627 (.Dup ⟨0, by decide⟩),
   pushAt 2628 0 0,
   opAt 2629 .SUB,
   opAt 2630 (.Dup ⟨1, by decide⟩),
   opAt 2631 (.Swap ⟨0, by decide⟩),
   opAt 2632 .MOD,
   pushAt 2633 2 1632,
   opAt 2634 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2635 (.Dup ⟨0, by decide⟩),
   pushAt 2636 1 2,
   opAt 2637 .SUB,
   opAt 2638 (.Dup ⟨0, by decide⟩),
   opAt 2639 (.Dup ⟨2, by decide⟩),
   opAt 2640 .MUL,
   pushAt 2641 1 2,
   opAt 2642 .SUB,
   opAt 2643 .MUL,
   opAt 2644 (.Dup ⟨0, by decide⟩),
   opAt 2645 (.Dup ⟨2, by decide⟩),
   opAt 2646 .MUL,
   pushAt 2647 1 2,
   opAt 2648 .SUB,
   opAt 2649 .MUL,
   opAt 2650 (.Dup ⟨0, by decide⟩),
   opAt 2651 (.Dup ⟨2, by decide⟩),
   opAt 2652 .MUL,
   pushAt 2653 1 2,
   opAt 2654 .SUB,
   opAt 2655 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2656 (.Dup ⟨0, by decide⟩),
   opAt 2657 (.Dup ⟨2, by decide⟩),
   opAt 2658 .MUL,
   pushAt 2659 1 2,
   opAt 2660 .SUB,
   opAt 2661 .MUL,
   opAt 2662 (.Dup ⟨0, by decide⟩),
   opAt 2663 (.Dup ⟨2, by decide⟩),
   opAt 2664 .MUL,
   pushAt 2665 1 2,
   opAt 2666 .SUB,
   opAt 2667 .MUL,
   opAt 2668 (.Dup ⟨0, by decide⟩),
   opAt 2669 (.Dup ⟨2, by decide⟩),
   opAt 2670 .MUL,
   pushAt 2671 1 2,
   opAt 2672 .SUB,
   opAt 2673 .MUL,
   opAt 2674 (.Dup ⟨0, by decide⟩),
   opAt 2675 (.Dup ⟨2, by decide⟩),
   opAt 2676 .MUL,
   pushAt 2677 1 2,
   opAt 2678 .SUB,
   opAt 2679 .MUL,
   pushAt 2680 2 1664,
   opAt 2681 .MSTORE,
   opAt 2682 .POP,
   opAt 2683 .POP,
   opAt 2684 .POP,
   opAt 2685 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2697 .JUMPDEST,
   opAt 2698 (.Dup ⟨0, by decide⟩),
   opAt 2699 .ISZERO,
   pushAt 2700 2 4075,
   opAt 2701 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2702 (.Dup ⟨1, by decide⟩),
   pushAt 2703 2 512,
   pushAt 2704 2 2080,
   opAt 2705 .MCOPY,
   pushAt 2706 0 0,
   pushAt 2707 2 2784,
   opAt 2708 .MLOAD,
   opAt 2709 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2710 2 512,
   opAt 2711 .MLOAD,
   pushAt 2712 2 1536,
   opAt 2713 .MLOAD,
   opAt 2714 (.Dup ⟨0, by decide⟩),
   opAt 2715 (.Dup ⟨2, by decide⟩),
   opAt 2716 .DIV,
   opAt 2717 (.Swap ⟨1, by decide⟩),
   opAt 2718 .MOD,
   pushAt 2719 2 1600,
   opAt 2720 .MLOAD,
   opAt 2721 .MUL,
   pushAt 2722 2 544,
   opAt 2723 .MLOAD,
   pushAt 2724 2 1536,
   opAt 2725 .MLOAD,
   opAt 2726 (.Swap ⟨0, by decide⟩),
   opAt 2727 .DIV,
   opAt 2728 .ADD,
   pushAt 2729 2 1568,
   opAt 2730 .MLOAD,
   opAt 2731 (.Dup ⟨0, by decide⟩),
   pushAt 2732 2 1632,
   opAt 2733 .MLOAD,
   opAt 2734 (.Dup ⟨4, by decide⟩),
   opAt 2735 .MULMOD,
   opAt 2736 (.Dup ⟨2, by decide⟩),
   opAt 2737 .ADDMOD,
   opAt 2738 (.Swap ⟨0, by decide⟩),
   opAt 2739 .SUB,
   pushAt 2740 2 1664,
   opAt 2741 .MLOAD,
   opAt 2742 .MUL,
   opAt 2743 (.Dup ⟨0, by decide⟩),
   pushAt 2744 0 0,
   opAt 2745 .MLOAD,
   opAt 2746 .MUL,
   pushAt 2747 2 544,
   opAt 2748 .MLOAD,
   opAt 2749 .SUB,
   pushAt 2750 1 32,
   opAt 2751 .MLOAD,
   pushAt 2752 1 128,
   opAt 2753 .SHR,
   opAt 2754 (.Dup ⟨2, by decide⟩),
   pushAt 2755 1 128,
   opAt 2756 .SHR,
   opAt 2757 .MUL,
   opAt 2758 .GT,
   opAt 2759 (.Swap ⟨0, by decide⟩),
   opAt 2760 .SUB,
   opAt 2761 (.Swap ⟨0, by decide⟩),
   pushAt 2762 2 1568,
   opAt 2763 .MLOAD,
   opAt 2764 .GT,
   opAt 2765 .ISZERO,
   pushAt 2766 0 0,
   opAt 2767 .SUB,
   opAt 2768 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2769 0 0,
   pushAt 2770 1 31,
   opAt 2771 .NOT,
   pushAt 2772 2 2784,
   opAt 2773 .MLOAD,
   pushAt 2774 2 2752,
   opAt 2775 .MLOAD,
   pushAt 2776 2 1280,
   opAt 2777 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2781 .JUMPDEST,
   opAt 2782 (.Dup ⟨0, by decide⟩),
   opAt 2783 .MLOAD,
   pushAt 2784 0 0,
   opAt 2785 .NOT,
   opAt 2786 (.Dup ⟨6, by decide⟩),
   opAt 2787 (.Dup ⟨2, by decide⟩),
   opAt 2788 .MUL,
   opAt 2789 (.Swap ⟨1, by decide⟩),
   opAt 2790 (.Dup ⟨7, by decide⟩),
   opAt 2791 .MULMOD,
   opAt 2792 (.Dup ⟨1, by decide⟩),
   opAt 2793 (.Dup ⟨1, by decide⟩),
   opAt 2794 .LT,
   opAt 2795 .SUB,
   opAt 2796 (.Dup ⟨5, by decide⟩),
   opAt 2797 (.Dup ⟨2, by decide⟩),
   opAt 2798 .ADD,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   opAt 2800 (.Swap ⟨6, by decide⟩),
   opAt 2801 .GT,
   opAt 2802 .SUB,
   opAt 2803 .SUB,
   opAt 2804 (.Dup ⟨4, by decide⟩),
   opAt 2805 (.Dup ⟨3, by decide⟩),
   opAt 2806 .MLOAD,
   opAt 2807 .ADD,
   opAt 2808 (.Dup ⟨0, by decide⟩),
   opAt 2809 (.Swap ⟨5, by decide⟩),
   opAt 2810 .GT,
   opAt 2811 .ADD,
   opAt 2812 (.Swap ⟨3, by decide⟩),
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 (.Dup ⟨4, by decide⟩),
   opAt 2815 .ADD,
   opAt 2816 (.Swap ⟨2, by decide⟩),
   opAt 2817 .MSTORE,
   opAt 2818 (.Dup ⟨2, by decide⟩),
   opAt 2819 .ADD,
   pushAt 2937 2 2080,
   opAt 2938 (.Dup ⟨2, by decide⟩),
   opAt 2939 .GT,
   pushAt 2940 2 3721,
   opAt 2941 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2942 .POP,
   opAt 2943 .POP,
   opAt 2944 .POP,
   pushAt 2945 2 2080,
   opAt 2946 .MLOAD,
   opAt 2947 (.Dup ⟨1, by decide⟩),
   opAt 2948 .ADD,
   opAt 2949 (.Dup ⟨1, by decide⟩),
   opAt 2950 (.Dup ⟨1, by decide⟩),
   opAt 2951 .LT,
   opAt 2952 (.Swap ⟨1, by decide⟩),
   opAt 2953 .POP,
   opAt 2954 (.Dup ⟨2, by decide⟩),
   opAt 2955 (.Dup ⟨1, by decide⟩),
   opAt 2956 .LT,
   opAt 2957 (.Swap ⟨0, by decide⟩),
   opAt 2958 (.Dup ⟨3, by decide⟩),
   opAt 2959 (.Swap ⟨0, by decide⟩),
   opAt 2960 .SUB,
   opAt 2961 (.Dup ⟨0, by decide⟩),
   pushAt 2962 2 2080,
   opAt 2963 .MSTORE,
   opAt 2964 .POP,
   opAt 2965 .GT,
   opAt 2966 (.Swap ⟨0, by decide⟩),
   opAt 2967 .POP,
   opAt 2968 .ISZERO,
   pushAt 2969 2 3988,
   opAt 2970 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2971 .JUMPDEST,
   pushAt 2972 0 0,
   pushAt 2973 2 2784,
   opAt 2974 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2975 .JUMPDEST,
   opAt 2976 (.Dup ⟨0, by decide⟩),
   opAt 2977 .MLOAD,
   opAt 2978 (.Dup ⟨1, by decide⟩),
   pushAt 2979 2 2112,
   opAt 2980 (.Swap ⟨0, by decide⟩),
   opAt 2981 .SUB,
   opAt 2982 .MLOAD,
   opAt 2983 (.Dup ⟨1, by decide⟩),
   opAt 2984 .ADD,
   opAt 2985 (.Dup ⟨0, by decide⟩),
   opAt 2986 (.Dup ⟨2, by decide⟩),
   opAt 2987 .GT,
   opAt 2988 (.Swap ⟨1, by decide⟩),
   opAt 2989 .POP,
   opAt 2990 (.Dup ⟨3, by decide⟩),
   opAt 2991 .ADD,
   opAt 2992 (.Dup ⟨0, by decide⟩),
   opAt 2993 (.Dup ⟨4, by decide⟩),
   opAt 2994 .GT,
   opAt 2995 (.Swap ⟨3, by decide⟩),
   opAt 2996 .POP,
   opAt 2997 (.Dup ⟨2, by decide⟩),
   opAt 2998 .MSTORE,
   opAt 2999 (.Swap ⟨0, by decide⟩),
   opAt 3000 (.Swap ⟨1, by decide⟩),
   opAt 3001 .OR,
   opAt 3002 (.Swap ⟨0, by decide⟩),
   pushAt 3003 1 31,
   opAt 3004 .NOT,
   opAt 3005 .ADD,
   pushAt 3006 2 2111,
   opAt 3007 (.Dup ⟨1, by decide⟩),
   opAt 3008 .GT,
   pushAt 3009 2 3927,
   opAt 3010 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3011 .POP,
   pushAt 3012 2 2080,
   opAt 3013 .MLOAD,
   opAt 3014 (.Dup ⟨1, by decide⟩),
   opAt 3015 .ADD,
   opAt 3016 (.Dup ⟨0, by decide⟩),
   pushAt 3017 2 2080,
   opAt 3018 .MSTORE,
   opAt 3019 .LT,
   opAt 3020 .ISZERO,
   pushAt 3021 2 3921,
   opAt 3022 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3023 .JUMPDEST,
   pushAt 3024 2 2080,
   opAt 3025 .MLOAD,
   opAt 3026 .ISZERO,
   pushAt 3027 2 4056,
   opAt 3028 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3029 0 0,
   pushAt 3030 2 2784,
   opAt 3031 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3032 .JUMPDEST,
   opAt 3033 (.Dup ⟨0, by decide⟩),
   opAt 3034 .MLOAD,
   pushAt 3035 2 2112,
   opAt 3036 (.Dup ⟨2, by decide⟩),
   opAt 3037 .SUB,
   opAt 3038 .MLOAD,
   opAt 3039 (.Dup ⟨1, by decide⟩),
   opAt 3040 (.Dup ⟨1, by decide⟩),
   opAt 3041 .GT,
   opAt 3042 (.Swap ⟨1, by decide⟩),
   opAt 3043 .SUB,
   opAt 3044 (.Dup ⟨3, by decide⟩),
   opAt 3045 (.Dup ⟨1, by decide⟩),
   opAt 3046 .LT,
   opAt 3047 (.Swap ⟨0, by decide⟩),
   opAt 3048 (.Dup ⟨4, by decide⟩),
   opAt 3049 (.Swap ⟨0, by decide⟩),
   opAt 3050 .SUB,
   opAt 3051 (.Dup ⟨3, by decide⟩),
   opAt 3052 .MSTORE,
   opAt 3053 .OR,
   opAt 3054 (.Swap ⟨1, by decide⟩),
   opAt 3055 .POP,
   pushAt 3056 1 31,
   opAt 3057 .NOT,
   opAt 3058 .ADD,
   pushAt 3059 2 2111,
   opAt 3060 (.Dup ⟨1, by decide⟩),
   opAt 3061 .GT,
   pushAt 3062 2 4003,
   opAt 3063 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3064 .POP,
   pushAt 3065 2 2080,
   opAt 3066 .MLOAD,
   opAt 3067 .SUB,
   pushAt 3068 2 2080,
   opAt 3069 .MSTORE,
   pushAt 3070 2 3988,
   opAt 3071 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3072 .JUMPDEST,
   pushAt 3073 2 4067,
   pushAt 3074 2 512,
   pushAt 3075 2 4877,
   opAt 3076 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3077 .JUMPDEST,
   pushAt 3078 0 0,
   opAt 3079 .NOT,
   opAt 3080 .ADD,
   pushAt 3081 2 3597,
   opAt 3082 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3083 .JUMPDEST,
   opAt 3084 .POP,
   pushAt 3085 2 2688,
   opAt 3086 .MLOAD,
   pushAt 3087 2 1280,
   pushAt 3088 2 1024,
   opAt 3089 .MCOPY,
   pushAt 3090 2 3216,
   opAt 3091 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3374 = true :=
  Artifact.isValidJumpDest_index 2535 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3418 = true :=
  Artifact.isValidJumpDest_index 2562 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3435 = true :=
  Artifact.isValidJumpDest_index 2570 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3442 = true :=
  Artifact.isValidJumpDest_index 2574 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3473 = true :=
  Artifact.isValidJumpDest_index 2598 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3597 = true :=
  Artifact.isValidJumpDest_index 2697 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3721 = true :=
  Artifact.isValidJumpDest_index 2781 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3921 = true :=
  Artifact.isValidJumpDest_index 2971 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3927 = true :=
  Artifact.isValidJumpDest_index 2975 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3988 = true :=
  Artifact.isValidJumpDest_index 3023 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4003 = true :=
  Artifact.isValidJumpDest_index 3032 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4056 = true :=
  Artifact.isValidJumpDest_index 3072 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4067 = true :=
  Artifact.isValidJumpDest_index 3077 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4075 = true :=
  Artifact.isValidJumpDest_index 3083 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
