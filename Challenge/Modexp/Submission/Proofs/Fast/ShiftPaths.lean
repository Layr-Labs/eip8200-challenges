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
  [opAt 2528 .JUMPDEST,
   opAt 2529 (.Dup ⟨0, by decide⟩),
   opAt 2530 (.Dup ⟨3, by decide⟩),
   opAt 2531 .EQ,
   pushAt 2532 0 0,
   opAt 2533 .MLOAD,
   pushAt 2534 1 255,
   opAt 2535 .SHR,
   opAt 2536 .AND,
   opAt 2537 .ISZERO,
   pushAt 2538 2 3418,
   opAt 2539 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2540 (.Dup ⟨0, by decide⟩),
   pushAt 2541 1 96,
   pushAt 2542 2 256,
   opAt 2543 .CALLDATACOPY,
   opAt 2544 (.Dup ⟨0, by decide⟩),
   pushAt 2545 1 96,
   pushAt 2546 2 2112,
   opAt 2547 .CALLDATACOPY,
   pushAt 2548 0 0,
   pushAt 2549 2 2080,
   opAt 2550 .MSTORE,
   pushAt 2551 2 3435,
   pushAt 2552 2 512,
   pushAt 2553 2 4877,
   opAt 2554 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2555 .JUMPDEST,
   pushAt 2556 1 1,
   pushAt 2557 2 1024,
   opAt 2558 .MSTORE,
   pushAt 2559 2 1430,
   pushAt 2560 2 1024,
   pushAt 2561 2 2208,
   opAt 2562 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2563 .JUMPDEST,
   pushAt 2564 1 1,
   pushAt 2565 2 2752,
   opAt 2566 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2567 .JUMPDEST,
   opAt 2568 (.Dup ⟨0, by decide⟩),
   opAt 2569 .MLOAD,
   opAt 2570 .NOT,
   opAt 2571 (.Dup ⟨2, by decide⟩),
   opAt 2572 .ADD,
   opAt 2573 (.Dup ⟨2, by decide⟩),
   opAt 2574 (.Dup ⟨1, by decide⟩),
   opAt 2575 .LT,
   opAt 2576 (.Swap ⟨2, by decide⟩),
   opAt 2577 .POP,
   opAt 2578 (.Dup ⟨1, by decide⟩),
   pushAt 2579 2 1280,
   opAt 2580 .ADD,
   opAt 2581 .MSTORE,
   opAt 2582 (.Dup ⟨0, by decide⟩),
   opAt 2583 .ISZERO,
   pushAt 2584 2 3473,
   opAt 2585 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2586 1 31,
   opAt 2587 .NOT,
   opAt 2588 .ADD,
   pushAt 2589 2 3442,
   opAt 2590 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2591 .JUMPDEST,
   opAt 2592 .POP,
   opAt 2593 .POP,
   pushAt 2594 0 0,
   opAt 2595 .MLOAD,
   opAt 2596 (.Dup ⟨0, by decide⟩),
   pushAt 2597 0 0,
   opAt 2598 .SUB,
   opAt 2599 (.Dup ⟨1, by decide⟩),
   opAt 2600 .AND,
   opAt 2601 (.Dup ⟨0, by decide⟩),
   pushAt 2602 2 1536,
   opAt 2603 .MSTORE,
   opAt 2604 (.Dup ⟨0, by decide⟩),
   opAt 2605 (.Dup ⟨2, by decide⟩),
   opAt 2606 .DIV,
   opAt 2607 (.Dup ⟨0, by decide⟩),
   pushAt 2608 2 1568,
   opAt 2609 .MSTORE,
   opAt 2610 (.Dup ⟨1, by decide⟩),
   pushAt 2611 0 0,
   opAt 2612 .SUB,
   opAt 2613 (.Dup ⟨2, by decide⟩),
   opAt 2614 (.Swap ⟨0, by decide⟩),
   opAt 2615 .DIV,
   pushAt 2616 1 1,
   opAt 2617 .ADD,
   pushAt 2618 2 1600,
   opAt 2619 .MSTORE,
   opAt 2620 (.Dup ⟨0, by decide⟩),
   pushAt 2621 0 0,
   opAt 2622 .SUB,
   opAt 2623 (.Dup ⟨1, by decide⟩),
   opAt 2624 (.Swap ⟨0, by decide⟩),
   opAt 2625 .MOD,
   pushAt 2626 2 1632,
   opAt 2627 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2628 (.Dup ⟨0, by decide⟩),
   pushAt 2629 1 3,
   opAt 2630 .MUL,
   pushAt 2631 1 2,
   opAt 2632 .XOR,
   opAt 2633 (.Dup ⟨0, by decide⟩),
   opAt 2634 (.Dup ⟨2, by decide⟩),
   opAt 2635 .MUL,
   pushAt 2636 1 2,
   opAt 2637 .SUB,
   opAt 2638 .MUL,
   opAt 2639 (.Dup ⟨0, by decide⟩),
   opAt 2640 (.Dup ⟨2, by decide⟩),
   opAt 2641 .MUL,
   pushAt 2642 1 2,
   opAt 2643 .SUB,
   opAt 2644 .MUL,
   opAt 2645 (.Dup ⟨0, by decide⟩),
   opAt 2646 (.Dup ⟨2, by decide⟩),
   opAt 2647 .MUL,
   pushAt 2648 1 2,
   opAt 2649 .SUB,
   opAt 2650 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2651 (.Dup ⟨0, by decide⟩),
   opAt 2652 (.Dup ⟨2, by decide⟩),
   opAt 2653 .MUL,
   pushAt 2654 1 2,
   opAt 2655 .SUB,
   opAt 2656 .MUL,
   opAt 2657 (.Dup ⟨0, by decide⟩),
   opAt 2658 (.Dup ⟨2, by decide⟩),
   opAt 2659 .MUL,
   pushAt 2660 1 2,
   opAt 2661 .SUB,
   opAt 2662 .MUL,
   opAt 2663 (.Dup ⟨0, by decide⟩),
   opAt 2664 (.Dup ⟨2, by decide⟩),
   opAt 2665 .MUL,
   pushAt 2666 1 2,
   opAt 2667 .SUB,
   opAt 2668 .MUL,
   pushAt 2669 6 1664,
   opAt 2670 .MSTORE,
   opAt 2671 .POP,
   opAt 2672 .POP,
   opAt 2673 .POP,
   opAt 2674 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2686 .JUMPDEST,
   opAt 2687 (.Dup ⟨0, by decide⟩),
   opAt 2688 .ISZERO,
   pushAt 2689 2 4075,
   opAt 2690 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2691 (.Dup ⟨1, by decide⟩),
   pushAt 2692 2 512,
   pushAt 2693 2 2080,
   opAt 2694 .MCOPY,
   pushAt 2695 0 0,
   pushAt 2696 2 2784,
   opAt 2697 .MLOAD,
   opAt 2698 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2699 2 512,
   opAt 2700 .MLOAD,
   pushAt 2701 2 1536,
   opAt 2702 .MLOAD,
   opAt 2703 (.Dup ⟨0, by decide⟩),
   opAt 2704 (.Dup ⟨2, by decide⟩),
   opAt 2705 .DIV,
   opAt 2706 (.Swap ⟨1, by decide⟩),
   opAt 2707 .MOD,
   pushAt 2708 2 1600,
   opAt 2709 .MLOAD,
   opAt 2710 .MUL,
   pushAt 2711 2 544,
   opAt 2712 .MLOAD,
   pushAt 2713 2 1536,
   opAt 2714 .MLOAD,
   opAt 2715 (.Swap ⟨0, by decide⟩),
   opAt 2716 .DIV,
   opAt 2717 .ADD,
   pushAt 2718 2 1568,
   opAt 2719 .MLOAD,
   opAt 2720 (.Dup ⟨0, by decide⟩),
   pushAt 2721 2 1632,
   opAt 2722 .MLOAD,
   opAt 2723 (.Dup ⟨4, by decide⟩),
   opAt 2724 .MULMOD,
   opAt 2725 (.Dup ⟨2, by decide⟩),
   opAt 2726 .ADDMOD,
   opAt 2727 (.Swap ⟨0, by decide⟩),
   opAt 2728 .SUB,
   pushAt 2729 2 1664,
   opAt 2730 .MLOAD,
   opAt 2731 .MUL,
   opAt 2732 (.Dup ⟨0, by decide⟩),
   pushAt 2733 0 0,
   opAt 2734 .MLOAD,
   opAt 2735 .MUL,
   pushAt 2736 2 544,
   opAt 2737 .MLOAD,
   opAt 2738 .SUB,
   pushAt 2739 1 32,
   opAt 2740 .MLOAD,
   pushAt 2741 1 128,
   opAt 2742 .SHR,
   opAt 2743 (.Dup ⟨2, by decide⟩),
   pushAt 2744 1 128,
   opAt 2745 .SHR,
   opAt 2746 .MUL,
   opAt 2747 .GT,
   opAt 2748 (.Swap ⟨0, by decide⟩),
   opAt 2749 .SUB,
   opAt 2750 (.Swap ⟨0, by decide⟩),
   pushAt 2751 2 1568,
   opAt 2752 .MLOAD,
   opAt 2753 .GT,
   opAt 2754 .ISZERO,
   pushAt 2755 0 0,
   opAt 2756 .SUB,
   opAt 2757 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2758 0 0,
   pushAt 2759 1 31,
   opAt 2760 .NOT,
   pushAt 2761 7 2784,
   opAt 2762 .MLOAD,
   pushAt 2763 0 0,
   opAt 2764 .NOT,
   opAt 2765 (.Swap ⟨0, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2769 .JUMPDEST,
   pushAt 2770 2 832,
   opAt 2771 (.Dup ⟨1, by decide⟩),
   opAt 2772 .SUB,
   opAt 2773 .MLOAD,
   opAt 2774 (.Dup ⟨2, by decide⟩),
   opAt 2775 (.Dup ⟨6, by decide⟩),
   opAt 2776 (.Dup ⟨2, by decide⟩),
   opAt 2777 .MUL,
   opAt 2778 (.Swap ⟨1, by decide⟩),
   opAt 2779 (.Dup ⟨7, by decide⟩),
   opAt 2780 .MULMOD,
   opAt 2781 (.Dup ⟨1, by decide⟩),
   opAt 2782 (.Dup ⟨1, by decide⟩),
   opAt 2783 .LT,
   opAt 2784 .SUB,
   opAt 2785 (.Dup ⟨5, by decide⟩),
   opAt 2786 (.Dup ⟨2, by decide⟩),
   opAt 2787 .ADD,
   opAt 2788 (.Dup ⟨0, by decide⟩),
   opAt 2789 (.Swap ⟨6, by decide⟩),
   opAt 2790 .GT,
   opAt 2791 .SUB,
   opAt 2792 .SUB,
   opAt 2793 (.Dup ⟨4, by decide⟩),
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .MLOAD,
   opAt 2796 .ADD,
   opAt 2797 (.Dup ⟨0, by decide⟩),
   opAt 2798 (.Swap ⟨5, by decide⟩),
   opAt 2799 .GT,
   opAt 2800 .ADD,
   opAt 2801 (.Swap ⟨3, by decide⟩),
   opAt 2802 (.Dup ⟨1, by decide⟩),
   opAt 2803 .MSTORE,
   opAt 2804 (.Dup ⟨2, by decide⟩),
   opAt 2805 .ADD,
   pushAt 2917 2 2080,
   opAt 2918 (.Dup ⟨1, by decide⟩),
   opAt 2919 .GT,
   pushAt 2920 2 3721,
   opAt 2921 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2922 .POP,
   opAt 2923 .POP,
   opAt 2924 .POP,
   pushAt 2925 2 2080,
   opAt 2926 .MLOAD,
   opAt 2927 (.Dup ⟨1, by decide⟩),
   opAt 2928 .ADD,
   opAt 2929 (.Dup ⟨1, by decide⟩),
   opAt 2930 (.Dup ⟨1, by decide⟩),
   opAt 2931 .LT,
   opAt 2932 (.Swap ⟨1, by decide⟩),
   opAt 2933 .POP,
   opAt 2934 (.Dup ⟨2, by decide⟩),
   opAt 2935 (.Dup ⟨1, by decide⟩),
   opAt 2936 .LT,
   opAt 2937 (.Swap ⟨0, by decide⟩),
   opAt 2938 (.Dup ⟨3, by decide⟩),
   opAt 2939 (.Swap ⟨0, by decide⟩),
   opAt 2940 .SUB,
   opAt 2941 (.Dup ⟨0, by decide⟩),
   pushAt 2942 2 2080,
   opAt 2943 .MSTORE,
   opAt 2944 .POP,
   opAt 2945 .GT,
   opAt 2946 (.Swap ⟨0, by decide⟩),
   opAt 2947 .POP,
   opAt 2948 .ISZERO,
   pushAt 2949 2 3988,
   opAt 2950 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2951 .JUMPDEST,
   pushAt 2952 0 0,
   pushAt 2953 2 2784,
   opAt 2954 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2955 .JUMPDEST,
   opAt 2956 (.Dup ⟨0, by decide⟩),
   opAt 2957 .MLOAD,
   opAt 2958 (.Dup ⟨1, by decide⟩),
   pushAt 2959 2 2112,
   opAt 2960 (.Swap ⟨0, by decide⟩),
   opAt 2961 .SUB,
   opAt 2962 .MLOAD,
   opAt 2963 (.Dup ⟨1, by decide⟩),
   opAt 2964 .ADD,
   opAt 2965 (.Dup ⟨0, by decide⟩),
   opAt 2966 (.Dup ⟨2, by decide⟩),
   opAt 2967 .GT,
   opAt 2968 (.Swap ⟨1, by decide⟩),
   opAt 2969 .POP,
   opAt 2970 (.Dup ⟨3, by decide⟩),
   opAt 2971 .ADD,
   opAt 2972 (.Dup ⟨0, by decide⟩),
   opAt 2973 (.Dup ⟨4, by decide⟩),
   opAt 2974 .GT,
   opAt 2975 (.Swap ⟨3, by decide⟩),
   opAt 2976 .POP,
   opAt 2977 (.Dup ⟨2, by decide⟩),
   opAt 2978 .MSTORE,
   opAt 2979 (.Swap ⟨0, by decide⟩),
   opAt 2980 (.Swap ⟨1, by decide⟩),
   opAt 2981 .OR,
   opAt 2982 (.Swap ⟨0, by decide⟩),
   pushAt 2983 1 31,
   opAt 2984 .NOT,
   opAt 2985 .ADD,
   pushAt 2986 2 2111,
   opAt 2987 (.Dup ⟨1, by decide⟩),
   opAt 2988 .GT,
   pushAt 2989 2 3927,
   opAt 2990 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2991 .POP,
   pushAt 2992 2 2080,
   opAt 2993 .MLOAD,
   opAt 2994 (.Dup ⟨1, by decide⟩),
   opAt 2995 .ADD,
   opAt 2996 (.Dup ⟨0, by decide⟩),
   pushAt 2997 2 2080,
   opAt 2998 .MSTORE,
   opAt 2999 .LT,
   opAt 3000 .ISZERO,
   pushAt 3001 2 3921,
   opAt 3002 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3003 .JUMPDEST,
   pushAt 3004 2 2080,
   opAt 3005 .MLOAD,
   opAt 3006 .ISZERO,
   pushAt 3007 2 4056,
   opAt 3008 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3009 0 0,
   pushAt 3010 2 2784,
   opAt 3011 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3012 .JUMPDEST,
   opAt 3013 (.Dup ⟨0, by decide⟩),
   opAt 3014 .MLOAD,
   pushAt 3015 2 2112,
   opAt 3016 (.Dup ⟨2, by decide⟩),
   opAt 3017 .SUB,
   opAt 3018 .MLOAD,
   opAt 3019 (.Dup ⟨1, by decide⟩),
   opAt 3020 (.Dup ⟨1, by decide⟩),
   opAt 3021 .GT,
   opAt 3022 (.Swap ⟨1, by decide⟩),
   opAt 3023 .SUB,
   opAt 3024 (.Dup ⟨3, by decide⟩),
   opAt 3025 (.Dup ⟨1, by decide⟩),
   opAt 3026 .LT,
   opAt 3027 (.Swap ⟨0, by decide⟩),
   opAt 3028 (.Dup ⟨4, by decide⟩),
   opAt 3029 (.Swap ⟨0, by decide⟩),
   opAt 3030 .SUB,
   opAt 3031 (.Dup ⟨3, by decide⟩),
   opAt 3032 .MSTORE,
   opAt 3033 .OR,
   opAt 3034 (.Swap ⟨1, by decide⟩),
   opAt 3035 .POP,
   pushAt 3036 1 31,
   opAt 3037 .NOT,
   opAt 3038 .ADD,
   pushAt 3039 2 2111,
   opAt 3040 (.Dup ⟨1, by decide⟩),
   opAt 3041 .GT,
   pushAt 3042 2 4003,
   opAt 3043 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3044 .POP,
   pushAt 3045 2 2080,
   opAt 3046 .MLOAD,
   opAt 3047 .SUB,
   pushAt 3048 2 2080,
   opAt 3049 .MSTORE,
   pushAt 3050 2 3988,
   opAt 3051 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3052 .JUMPDEST,
   pushAt 3053 2 4067,
   pushAt 3054 2 512,
   pushAt 3055 2 4877,
   opAt 3056 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3057 .JUMPDEST,
   pushAt 3058 0 0,
   opAt 3059 .NOT,
   opAt 3060 .ADD,
   pushAt 3061 2 3597,
   opAt 3062 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3063 .JUMPDEST,
   opAt 3064 .POP,
   pushAt 3065 2 2688,
   opAt 3066 .MLOAD,
   pushAt 3067 2 1280,
   pushAt 3068 2 1024,
   opAt 3069 .MCOPY,
   pushAt 3070 2 3216,
   opAt 3071 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3374 = true :=
  Artifact.isValidJumpDest_index 2528 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3418 = true :=
  Artifact.isValidJumpDest_index 2555 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3435 = true :=
  Artifact.isValidJumpDest_index 2563 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3442 = true :=
  Artifact.isValidJumpDest_index 2567 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3473 = true :=
  Artifact.isValidJumpDest_index 2591 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3597 = true :=
  Artifact.isValidJumpDest_index 2686 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3721 = true :=
  Artifact.isValidJumpDest_index 2769 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3921 = true :=
  Artifact.isValidJumpDest_index 2951 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3927 = true :=
  Artifact.isValidJumpDest_index 2955 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3988 = true :=
  Artifact.isValidJumpDest_index 3003 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4003 = true :=
  Artifact.isValidJumpDest_index 3012 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4056 = true :=
  Artifact.isValidJumpDest_index 3052 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4067 = true :=
  Artifact.isValidJumpDest_index 3057 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4075 = true :=
  Artifact.isValidJumpDest_index 3063 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
