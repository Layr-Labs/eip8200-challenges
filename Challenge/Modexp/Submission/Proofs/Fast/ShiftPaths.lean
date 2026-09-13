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
  [opAt 2533 .JUMPDEST,
   opAt 2534 (.Dup ⟨0, by decide⟩),
   opAt 2535 (.Dup ⟨3, by decide⟩),
   opAt 2536 .EQ,
   pushAt 2537 0 0,
   opAt 2538 .MLOAD,
   pushAt 2539 1 255,
   opAt 2540 .SHR,
   opAt 2541 .AND,
   opAt 2542 .ISZERO,
   pushAt 2543 2 3418,
   opAt 2544 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2545 (.Dup ⟨0, by decide⟩),
   pushAt 2546 1 96,
   pushAt 2547 2 256,
   opAt 2548 .CALLDATACOPY,
   opAt 2549 (.Dup ⟨0, by decide⟩),
   pushAt 2550 1 96,
   pushAt 2551 2 2112,
   opAt 2552 .CALLDATACOPY,
   pushAt 2553 0 0,
   pushAt 2554 2 2080,
   opAt 2555 .MSTORE,
   pushAt 2556 2 3435,
   pushAt 2557 2 512,
   pushAt 2558 2 4877,
   opAt 2559 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2560 .JUMPDEST,
   pushAt 2561 1 1,
   pushAt 2562 2 1024,
   opAt 2563 .MSTORE,
   pushAt 2564 2 1430,
   pushAt 2565 2 1024,
   pushAt 2566 2 2208,
   opAt 2567 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2568 .JUMPDEST,
   pushAt 2569 1 1,
   pushAt 2570 2 2752,
   opAt 2571 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2572 .JUMPDEST,
   opAt 2573 (.Dup ⟨0, by decide⟩),
   opAt 2574 .MLOAD,
   opAt 2575 .NOT,
   opAt 2576 (.Dup ⟨2, by decide⟩),
   opAt 2577 .ADD,
   opAt 2578 (.Dup ⟨2, by decide⟩),
   opAt 2579 (.Dup ⟨1, by decide⟩),
   opAt 2580 .LT,
   opAt 2581 (.Swap ⟨2, by decide⟩),
   opAt 2582 .POP,
   opAt 2583 (.Dup ⟨1, by decide⟩),
   pushAt 2584 2 1280,
   opAt 2585 .ADD,
   opAt 2586 .MSTORE,
   opAt 2587 (.Dup ⟨0, by decide⟩),
   opAt 2588 .ISZERO,
   pushAt 2589 2 3473,
   opAt 2590 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2591 1 31,
   opAt 2592 .NOT,
   opAt 2593 .ADD,
   pushAt 2594 2 3442,
   opAt 2595 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2596 .JUMPDEST,
   opAt 2597 .POP,
   opAt 2598 .POP,
   pushAt 2599 0 0,
   opAt 2600 .MLOAD,
   opAt 2601 (.Dup ⟨0, by decide⟩),
   pushAt 2602 0 0,
   opAt 2603 .SUB,
   opAt 2604 (.Dup ⟨1, by decide⟩),
   opAt 2605 .AND,
   opAt 2606 (.Dup ⟨0, by decide⟩),
   pushAt 2607 2 1536,
   opAt 2608 .MSTORE,
   opAt 2609 (.Dup ⟨0, by decide⟩),
   opAt 2610 (.Dup ⟨2, by decide⟩),
   opAt 2611 .DIV,
   opAt 2612 (.Dup ⟨0, by decide⟩),
   pushAt 2613 2 1568,
   opAt 2614 .MSTORE,
   opAt 2615 (.Dup ⟨1, by decide⟩),
   pushAt 2616 0 0,
   opAt 2617 .SUB,
   opAt 2618 (.Dup ⟨2, by decide⟩),
   opAt 2619 (.Swap ⟨0, by decide⟩),
   opAt 2620 .DIV,
   pushAt 2621 1 1,
   opAt 2622 .ADD,
   pushAt 2623 2 1600,
   opAt 2624 .MSTORE,
   opAt 2625 (.Dup ⟨0, by decide⟩),
   pushAt 2626 0 0,
   opAt 2627 .SUB,
   opAt 2628 (.Dup ⟨1, by decide⟩),
   opAt 2629 (.Swap ⟨0, by decide⟩),
   opAt 2630 .MOD,
   pushAt 2631 2 1632,
   opAt 2632 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2633 (.Dup ⟨0, by decide⟩),
   pushAt 2634 1 2,
   opAt 2635 .SUB,
   opAt 2636 (.Dup ⟨0, by decide⟩),
   opAt 2637 (.Dup ⟨2, by decide⟩),
   opAt 2638 .MUL,
   pushAt 2639 1 2,
   opAt 2640 .SUB,
   opAt 2641 .MUL,
   opAt 2642 (.Dup ⟨0, by decide⟩),
   opAt 2643 (.Dup ⟨2, by decide⟩),
   opAt 2644 .MUL,
   pushAt 2645 1 2,
   opAt 2646 .SUB,
   opAt 2647 .MUL,
   opAt 2648 (.Dup ⟨0, by decide⟩),
   opAt 2649 (.Dup ⟨2, by decide⟩),
   opAt 2650 .MUL,
   pushAt 2651 1 2,
   opAt 2652 .SUB,
   opAt 2653 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2654 (.Dup ⟨0, by decide⟩),
   opAt 2655 (.Dup ⟨2, by decide⟩),
   opAt 2656 .MUL,
   pushAt 2657 1 2,
   opAt 2658 .SUB,
   opAt 2659 .MUL,
   opAt 2660 (.Dup ⟨0, by decide⟩),
   opAt 2661 (.Dup ⟨2, by decide⟩),
   opAt 2662 .MUL,
   pushAt 2663 1 2,
   opAt 2664 .SUB,
   opAt 2665 .MUL,
   opAt 2666 (.Dup ⟨0, by decide⟩),
   opAt 2667 (.Dup ⟨2, by decide⟩),
   opAt 2668 .MUL,
   pushAt 2669 1 2,
   opAt 2670 .SUB,
   opAt 2671 .MUL,
   opAt 2672 (.Dup ⟨0, by decide⟩),
   opAt 2673 (.Dup ⟨2, by decide⟩),
   opAt 2674 .MUL,
   pushAt 2675 1 2,
   opAt 2676 .SUB,
   opAt 2677 .MUL,
   pushAt 2678 2 1664,
   opAt 2679 .MSTORE,
   opAt 2680 .POP,
   opAt 2681 .POP,
   opAt 2682 .POP,
   opAt 2683 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2695 .JUMPDEST,
   opAt 2696 (.Dup ⟨0, by decide⟩),
   opAt 2697 .ISZERO,
   pushAt 2698 2 4075,
   opAt 2699 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2700 (.Dup ⟨1, by decide⟩),
   pushAt 2701 2 512,
   pushAt 2702 2 2080,
   opAt 2703 .MCOPY,
   pushAt 2704 0 0,
   pushAt 2705 2 2784,
   opAt 2706 .MLOAD,
   opAt 2707 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2708 2 512,
   opAt 2709 .MLOAD,
   pushAt 2710 2 1536,
   opAt 2711 .MLOAD,
   opAt 2712 (.Dup ⟨0, by decide⟩),
   opAt 2713 (.Dup ⟨2, by decide⟩),
   opAt 2714 .DIV,
   opAt 2715 (.Swap ⟨1, by decide⟩),
   opAt 2716 .MOD,
   pushAt 2717 2 1600,
   opAt 2718 .MLOAD,
   opAt 2719 .MUL,
   pushAt 2720 2 544,
   opAt 2721 .MLOAD,
   pushAt 2722 2 1536,
   opAt 2723 .MLOAD,
   opAt 2724 (.Swap ⟨0, by decide⟩),
   opAt 2725 .DIV,
   opAt 2726 .ADD,
   pushAt 2727 2 1568,
   opAt 2728 .MLOAD,
   opAt 2729 (.Dup ⟨0, by decide⟩),
   pushAt 2730 2 1632,
   opAt 2731 .MLOAD,
   opAt 2732 (.Dup ⟨4, by decide⟩),
   opAt 2733 .MULMOD,
   opAt 2734 (.Dup ⟨2, by decide⟩),
   opAt 2735 .ADDMOD,
   opAt 2736 (.Swap ⟨0, by decide⟩),
   opAt 2737 .SUB,
   pushAt 2738 2 1664,
   opAt 2739 .MLOAD,
   opAt 2740 .MUL,
   opAt 2741 (.Dup ⟨0, by decide⟩),
   pushAt 2742 0 0,
   opAt 2743 .MLOAD,
   opAt 2744 .MUL,
   pushAt 2745 2 544,
   opAt 2746 .MLOAD,
   opAt 2747 .SUB,
   pushAt 2748 1 32,
   opAt 2749 .MLOAD,
   pushAt 2750 1 128,
   opAt 2751 .SHR,
   opAt 2752 (.Dup ⟨2, by decide⟩),
   pushAt 2753 1 128,
   opAt 2754 .SHR,
   opAt 2755 .MUL,
   opAt 2756 .GT,
   opAt 2757 (.Swap ⟨0, by decide⟩),
   opAt 2758 .SUB,
   opAt 2759 (.Swap ⟨0, by decide⟩),
   pushAt 2760 2 1568,
   opAt 2761 .MLOAD,
   opAt 2762 .GT,
   opAt 2763 .ISZERO,
   pushAt 2764 0 0,
   opAt 2765 .SUB,
   opAt 2766 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2767 0 0,
   pushAt 2768 1 31,
   opAt 2769 .NOT,
   pushAt 2770 2 2784,
   opAt 2771 .MLOAD,
   pushAt 2772 2 2752,
   opAt 2773 .MLOAD,
   pushAt 2774 2 1280,
   opAt 2775 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2779 .JUMPDEST,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   opAt 2781 .MLOAD,
   pushAt 2782 0 0,
   opAt 2783 .NOT,
   opAt 2784 (.Dup ⟨6, by decide⟩),
   opAt 2785 (.Dup ⟨2, by decide⟩),
   opAt 2786 .MUL,
   opAt 2787 (.Swap ⟨1, by decide⟩),
   opAt 2788 (.Dup ⟨7, by decide⟩),
   opAt 2789 .MULMOD,
   opAt 2790 (.Dup ⟨1, by decide⟩),
   opAt 2791 (.Dup ⟨1, by decide⟩),
   opAt 2792 .LT,
   opAt 2793 .SUB,
   opAt 2794 (.Dup ⟨5, by decide⟩),
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .ADD,
   opAt 2797 (.Dup ⟨0, by decide⟩),
   opAt 2798 (.Swap ⟨6, by decide⟩),
   opAt 2799 .GT,
   opAt 2800 .SUB,
   opAt 2801 .SUB,
   opAt 2802 (.Dup ⟨4, by decide⟩),
   opAt 2803 (.Dup ⟨3, by decide⟩),
   opAt 2804 .MLOAD,
   opAt 2805 .ADD,
   opAt 2806 (.Dup ⟨0, by decide⟩),
   opAt 2807 (.Swap ⟨5, by decide⟩),
   opAt 2808 .GT,
   opAt 2809 .ADD,
   opAt 2810 (.Swap ⟨3, by decide⟩),
   opAt 2811 (.Dup ⟨2, by decide⟩),
   opAt 2812 (.Dup ⟨4, by decide⟩),
   opAt 2813 .ADD,
   opAt 2814 (.Swap ⟨2, by decide⟩),
   opAt 2815 .MSTORE,
   opAt 2816 (.Dup ⟨2, by decide⟩),
   opAt 2817 .ADD,
   pushAt 2935 2 2080,
   opAt 2936 (.Dup ⟨2, by decide⟩),
   opAt 2937 .GT,
   pushAt 2938 2 3721,
   opAt 2939 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2940 .POP,
   opAt 2941 .POP,
   opAt 2942 .POP,
   pushAt 2943 2 2080,
   opAt 2944 .MLOAD,
   opAt 2945 (.Dup ⟨1, by decide⟩),
   opAt 2946 .ADD,
   opAt 2947 (.Dup ⟨1, by decide⟩),
   opAt 2948 (.Dup ⟨1, by decide⟩),
   opAt 2949 .LT,
   opAt 2950 (.Swap ⟨1, by decide⟩),
   opAt 2951 .POP,
   opAt 2952 (.Dup ⟨2, by decide⟩),
   opAt 2953 (.Dup ⟨1, by decide⟩),
   opAt 2954 .LT,
   opAt 2955 (.Swap ⟨0, by decide⟩),
   opAt 2956 (.Dup ⟨3, by decide⟩),
   opAt 2957 (.Swap ⟨0, by decide⟩),
   opAt 2958 .SUB,
   opAt 2959 (.Dup ⟨0, by decide⟩),
   pushAt 2960 2 2080,
   opAt 2961 .MSTORE,
   opAt 2962 .POP,
   opAt 2963 .GT,
   opAt 2964 (.Swap ⟨0, by decide⟩),
   opAt 2965 .POP,
   opAt 2966 .ISZERO,
   pushAt 2967 2 3988,
   opAt 2968 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2969 .JUMPDEST,
   pushAt 2970 0 0,
   pushAt 2971 2 2784,
   opAt 2972 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2973 .JUMPDEST,
   opAt 2974 (.Dup ⟨0, by decide⟩),
   opAt 2975 .MLOAD,
   opAt 2976 (.Dup ⟨1, by decide⟩),
   pushAt 2977 2 2112,
   opAt 2978 (.Swap ⟨0, by decide⟩),
   opAt 2979 .SUB,
   opAt 2980 .MLOAD,
   opAt 2981 (.Dup ⟨1, by decide⟩),
   opAt 2982 .ADD,
   opAt 2983 (.Dup ⟨0, by decide⟩),
   opAt 2984 (.Dup ⟨2, by decide⟩),
   opAt 2985 .GT,
   opAt 2986 (.Swap ⟨1, by decide⟩),
   opAt 2987 .POP,
   opAt 2988 (.Dup ⟨3, by decide⟩),
   opAt 2989 .ADD,
   opAt 2990 (.Dup ⟨0, by decide⟩),
   opAt 2991 (.Dup ⟨4, by decide⟩),
   opAt 2992 .GT,
   opAt 2993 (.Swap ⟨3, by decide⟩),
   opAt 2994 .POP,
   opAt 2995 (.Dup ⟨2, by decide⟩),
   opAt 2996 .MSTORE,
   opAt 2997 (.Swap ⟨0, by decide⟩),
   opAt 2998 (.Swap ⟨1, by decide⟩),
   opAt 2999 .OR,
   opAt 3000 (.Swap ⟨0, by decide⟩),
   pushAt 3001 1 31,
   opAt 3002 .NOT,
   opAt 3003 .ADD,
   pushAt 3004 2 2111,
   opAt 3005 (.Dup ⟨1, by decide⟩),
   opAt 3006 .GT,
   pushAt 3007 2 3927,
   opAt 3008 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3009 .POP,
   pushAt 3010 2 2080,
   opAt 3011 .MLOAD,
   opAt 3012 (.Dup ⟨1, by decide⟩),
   opAt 3013 .ADD,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   pushAt 3015 2 2080,
   opAt 3016 .MSTORE,
   opAt 3017 .LT,
   opAt 3018 .ISZERO,
   pushAt 3019 2 3921,
   opAt 3020 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3021 .JUMPDEST,
   pushAt 3022 2 2080,
   opAt 3023 .MLOAD,
   opAt 3024 .ISZERO,
   pushAt 3025 2 4056,
   opAt 3026 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3027 0 0,
   pushAt 3028 2 2784,
   opAt 3029 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3030 .JUMPDEST,
   opAt 3031 (.Dup ⟨0, by decide⟩),
   opAt 3032 .MLOAD,
   pushAt 3033 2 2112,
   opAt 3034 (.Dup ⟨2, by decide⟩),
   opAt 3035 .SUB,
   opAt 3036 .MLOAD,
   opAt 3037 (.Dup ⟨1, by decide⟩),
   opAt 3038 (.Dup ⟨1, by decide⟩),
   opAt 3039 .GT,
   opAt 3040 (.Swap ⟨1, by decide⟩),
   opAt 3041 .SUB,
   opAt 3042 (.Dup ⟨3, by decide⟩),
   opAt 3043 (.Dup ⟨1, by decide⟩),
   opAt 3044 .LT,
   opAt 3045 (.Swap ⟨0, by decide⟩),
   opAt 3046 (.Dup ⟨4, by decide⟩),
   opAt 3047 (.Swap ⟨0, by decide⟩),
   opAt 3048 .SUB,
   opAt 3049 (.Dup ⟨3, by decide⟩),
   opAt 3050 .MSTORE,
   opAt 3051 .OR,
   opAt 3052 (.Swap ⟨1, by decide⟩),
   opAt 3053 .POP,
   pushAt 3054 1 31,
   opAt 3055 .NOT,
   opAt 3056 .ADD,
   pushAt 3057 2 2111,
   opAt 3058 (.Dup ⟨1, by decide⟩),
   opAt 3059 .GT,
   pushAt 3060 2 4003,
   opAt 3061 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3062 .POP,
   pushAt 3063 2 2080,
   opAt 3064 .MLOAD,
   opAt 3065 .SUB,
   pushAt 3066 2 2080,
   opAt 3067 .MSTORE,
   pushAt 3068 2 3988,
   opAt 3069 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3070 .JUMPDEST,
   pushAt 3071 2 4067,
   pushAt 3072 2 512,
   pushAt 3073 2 4877,
   opAt 3074 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3075 .JUMPDEST,
   pushAt 3076 0 0,
   opAt 3077 .NOT,
   opAt 3078 .ADD,
   pushAt 3079 2 3597,
   opAt 3080 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3081 .JUMPDEST,
   opAt 3082 .POP,
   pushAt 3083 2 2688,
   opAt 3084 .MLOAD,
   pushAt 3085 2 1280,
   pushAt 3086 2 1024,
   opAt 3087 .MCOPY,
   pushAt 3088 2 3216,
   opAt 3089 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3374 = true :=
  Artifact.isValidJumpDest_index 2533 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3418 = true :=
  Artifact.isValidJumpDest_index 2560 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3435 = true :=
  Artifact.isValidJumpDest_index 2568 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3442 = true :=
  Artifact.isValidJumpDest_index 2572 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3473 = true :=
  Artifact.isValidJumpDest_index 2596 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3597 = true :=
  Artifact.isValidJumpDest_index 2695 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3721 = true :=
  Artifact.isValidJumpDest_index 2779 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3921 = true :=
  Artifact.isValidJumpDest_index 2969 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3927 = true :=
  Artifact.isValidJumpDest_index 2973 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3988 = true :=
  Artifact.isValidJumpDest_index 3021 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4003 = true :=
  Artifact.isValidJumpDest_index 3030 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4056 = true :=
  Artifact.isValidJumpDest_index 3070 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4067 = true :=
  Artifact.isValidJumpDest_index 3075 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4075 = true :=
  Artifact.isValidJumpDest_index 3081 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
