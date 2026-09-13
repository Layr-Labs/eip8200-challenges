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
  [opAt 2529 .JUMPDEST,
   opAt 2530 (.Dup ⟨0, by decide⟩),
   opAt 2531 (.Dup ⟨3, by decide⟩),
   opAt 2532 .EQ,
   pushAt 2533 0 0,
   opAt 2534 .MLOAD,
   pushAt 2535 1 255,
   opAt 2536 .SHR,
   opAt 2537 .AND,
   opAt 2538 .ISZERO,
   pushAt 2539 2 3418,
   opAt 2540 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2541 (.Dup ⟨0, by decide⟩),
   pushAt 2542 1 96,
   pushAt 2543 2 256,
   opAt 2544 .CALLDATACOPY,
   opAt 2545 (.Dup ⟨0, by decide⟩),
   pushAt 2546 1 96,
   pushAt 2547 2 2112,
   opAt 2548 .CALLDATACOPY,
   pushAt 2549 0 0,
   pushAt 2550 2 2080,
   opAt 2551 .MSTORE,
   pushAt 2552 2 3435,
   pushAt 2553 2 512,
   pushAt 2554 2 4877,
   opAt 2555 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2556 .JUMPDEST,
   pushAt 2557 1 1,
   pushAt 2558 2 1024,
   opAt 2559 .MSTORE,
   pushAt 2560 2 1430,
   pushAt 2561 2 1024,
   pushAt 2562 2 2208,
   opAt 2563 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2564 .JUMPDEST,
   pushAt 2565 1 1,
   pushAt 2566 2 2752,
   opAt 2567 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2568 .JUMPDEST,
   opAt 2569 (.Dup ⟨0, by decide⟩),
   opAt 2570 .MLOAD,
   opAt 2571 .NOT,
   opAt 2572 (.Dup ⟨2, by decide⟩),
   opAt 2573 .ADD,
   opAt 2574 (.Dup ⟨2, by decide⟩),
   opAt 2575 (.Dup ⟨1, by decide⟩),
   opAt 2576 .LT,
   opAt 2577 (.Swap ⟨2, by decide⟩),
   opAt 2578 .POP,
   opAt 2579 (.Dup ⟨1, by decide⟩),
   pushAt 2580 2 1280,
   opAt 2581 .ADD,
   opAt 2582 .MSTORE,
   opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 .ISZERO,
   pushAt 2585 2 3473,
   opAt 2586 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2587 1 31,
   opAt 2588 .NOT,
   opAt 2589 .ADD,
   pushAt 2590 2 3442,
   opAt 2591 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2592 .JUMPDEST,
   opAt 2593 .POP,
   opAt 2594 .POP,
   pushAt 2595 0 0,
   opAt 2596 .MLOAD,
   opAt 2597 (.Dup ⟨0, by decide⟩),
   pushAt 2598 0 0,
   opAt 2599 .SUB,
   opAt 2600 (.Dup ⟨1, by decide⟩),
   opAt 2601 .AND,
   opAt 2602 (.Dup ⟨0, by decide⟩),
   pushAt 2603 2 1536,
   opAt 2604 .MSTORE,
   opAt 2605 (.Dup ⟨0, by decide⟩),
   opAt 2606 (.Dup ⟨2, by decide⟩),
   opAt 2607 .DIV,
   opAt 2608 (.Dup ⟨0, by decide⟩),
   pushAt 2609 2 1568,
   opAt 2610 .MSTORE,
   opAt 2611 (.Dup ⟨1, by decide⟩),
   pushAt 2612 0 0,
   opAt 2613 .SUB,
   opAt 2614 (.Dup ⟨2, by decide⟩),
   opAt 2615 (.Swap ⟨0, by decide⟩),
   opAt 2616 .DIV,
   pushAt 2617 1 1,
   opAt 2618 .ADD,
   pushAt 2619 2 1600,
   opAt 2620 .MSTORE,
   opAt 2621 (.Dup ⟨0, by decide⟩),
   pushAt 2622 0 0,
   opAt 2623 .SUB,
   opAt 2624 (.Dup ⟨1, by decide⟩),
   opAt 2625 (.Swap ⟨0, by decide⟩),
   opAt 2626 .MOD,
   pushAt 2627 2 1632,
   opAt 2628 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2629 (.Dup ⟨0, by decide⟩),
   pushAt 2630 1 3,
   opAt 2631 .MUL,
   pushAt 2632 1 2,
   opAt 2633 .XOR,
   opAt 2634 (.Dup ⟨0, by decide⟩),
   opAt 2635 (.Dup ⟨2, by decide⟩),
   opAt 2636 .MUL,
   pushAt 2637 1 2,
   opAt 2638 .SUB,
   opAt 2639 .MUL,
   opAt 2640 (.Dup ⟨0, by decide⟩),
   opAt 2641 (.Dup ⟨2, by decide⟩),
   opAt 2642 .MUL,
   pushAt 2643 1 2,
   opAt 2644 .SUB,
   opAt 2645 .MUL,
   opAt 2646 (.Dup ⟨0, by decide⟩),
   opAt 2647 (.Dup ⟨2, by decide⟩),
   opAt 2648 .MUL,
   pushAt 2649 1 2,
   opAt 2650 .SUB,
   opAt 2651 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2652 (.Dup ⟨0, by decide⟩),
   opAt 2653 (.Dup ⟨2, by decide⟩),
   opAt 2654 .MUL,
   pushAt 2655 1 2,
   opAt 2656 .SUB,
   opAt 2657 .MUL,
   opAt 2658 (.Dup ⟨0, by decide⟩),
   opAt 2659 (.Dup ⟨2, by decide⟩),
   opAt 2660 .MUL,
   pushAt 2661 1 2,
   opAt 2662 .SUB,
   opAt 2663 .MUL,
   opAt 2664 (.Dup ⟨0, by decide⟩),
   opAt 2665 (.Dup ⟨2, by decide⟩),
   opAt 2666 .MUL,
   pushAt 2667 1 2,
   opAt 2668 .SUB,
   opAt 2669 .MUL,
   pushAt 2670 6 1664,
   opAt 2671 .MSTORE,
   opAt 2672 .POP,
   opAt 2673 .POP,
   opAt 2674 .POP,
   opAt 2675 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2687 .JUMPDEST,
   opAt 2688 (.Dup ⟨0, by decide⟩),
   opAt 2689 .ISZERO,
   pushAt 2690 2 4075,
   opAt 2691 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2692 (.Dup ⟨1, by decide⟩),
   pushAt 2693 2 512,
   pushAt 2694 2 2080,
   opAt 2695 .MCOPY,
   pushAt 2696 0 0,
   pushAt 2697 2 2784,
   opAt 2698 .MLOAD,
   opAt 2699 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2700 2 512,
   opAt 2701 .MLOAD,
   pushAt 2702 2 1536,
   opAt 2703 .MLOAD,
   opAt 2704 (.Dup ⟨0, by decide⟩),
   opAt 2705 (.Dup ⟨2, by decide⟩),
   opAt 2706 .DIV,
   opAt 2707 (.Swap ⟨1, by decide⟩),
   opAt 2708 .MOD,
   pushAt 2709 2 1600,
   opAt 2710 .MLOAD,
   opAt 2711 .MUL,
   pushAt 2712 2 544,
   opAt 2713 .MLOAD,
   pushAt 2714 2 1536,
   opAt 2715 .MLOAD,
   opAt 2716 (.Swap ⟨0, by decide⟩),
   opAt 2717 .DIV,
   opAt 2718 .ADD,
   pushAt 2719 2 1568,
   opAt 2720 .MLOAD,
   opAt 2721 (.Dup ⟨0, by decide⟩),
   pushAt 2722 2 1632,
   opAt 2723 .MLOAD,
   opAt 2724 (.Dup ⟨4, by decide⟩),
   opAt 2725 .MULMOD,
   opAt 2726 (.Dup ⟨2, by decide⟩),
   opAt 2727 .ADDMOD,
   opAt 2728 (.Swap ⟨0, by decide⟩),
   opAt 2729 .SUB,
   pushAt 2730 2 1664,
   opAt 2731 .MLOAD,
   opAt 2732 .MUL,
   opAt 2733 (.Dup ⟨0, by decide⟩),
   pushAt 2734 0 0,
   opAt 2735 .MLOAD,
   opAt 2736 .MUL,
   pushAt 2737 2 544,
   opAt 2738 .MLOAD,
   opAt 2739 .SUB,
   pushAt 2740 1 32,
   opAt 2741 .MLOAD,
   pushAt 2742 1 128,
   opAt 2743 .SHR,
   opAt 2744 (.Dup ⟨2, by decide⟩),
   pushAt 2745 1 128,
   opAt 2746 .SHR,
   opAt 2747 .MUL,
   opAt 2748 .GT,
   opAt 2749 (.Swap ⟨0, by decide⟩),
   opAt 2750 .SUB,
   opAt 2751 (.Swap ⟨0, by decide⟩),
   pushAt 2752 2 1568,
   opAt 2753 .MLOAD,
   opAt 2754 .GT,
   opAt 2755 .ISZERO,
   pushAt 2756 0 0,
   opAt 2757 .SUB,
   opAt 2758 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2759 0 0,
   pushAt 2760 1 31,
   opAt 2761 .NOT,
   pushAt 2762 7 2784,
   opAt 2763 .MLOAD,
   pushAt 2764 0 0,
   opAt 2765 .NOT,
   opAt 2766 (.Swap ⟨0, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2770 .JUMPDEST,
   pushAt 2771 2 832,
   opAt 2772 (.Dup ⟨1, by decide⟩),
   opAt 2773 .SUB,
   opAt 2774 .MLOAD,
   opAt 2775 (.Dup ⟨2, by decide⟩),
   opAt 2776 (.Dup ⟨6, by decide⟩),
   opAt 2777 (.Dup ⟨2, by decide⟩),
   opAt 2778 .MUL,
   opAt 2779 (.Swap ⟨1, by decide⟩),
   opAt 2780 (.Dup ⟨7, by decide⟩),
   opAt 2781 .MULMOD,
   opAt 2782 (.Dup ⟨1, by decide⟩),
   opAt 2783 (.Dup ⟨1, by decide⟩),
   opAt 2784 .LT,
   opAt 2785 .SUB,
   opAt 2786 (.Dup ⟨5, by decide⟩),
   opAt 2787 (.Dup ⟨2, by decide⟩),
   opAt 2788 .ADD,
   opAt 2789 (.Dup ⟨0, by decide⟩),
   opAt 2790 (.Swap ⟨6, by decide⟩),
   opAt 2791 .GT,
   opAt 2792 .SUB,
   opAt 2793 .SUB,
   opAt 2794 (.Dup ⟨4, by decide⟩),
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .MLOAD,
   opAt 2797 .ADD,
   opAt 2798 (.Dup ⟨0, by decide⟩),
   opAt 2799 (.Swap ⟨5, by decide⟩),
   opAt 2800 .GT,
   opAt 2801 .ADD,
   opAt 2802 (.Swap ⟨3, by decide⟩),
   opAt 2803 (.Dup ⟨1, by decide⟩),
   opAt 2804 .MSTORE,
   opAt 2805 (.Dup ⟨2, by decide⟩),
   opAt 2806 .ADD,
   pushAt 2918 2 2080,
   opAt 2919 (.Dup ⟨1, by decide⟩),
   opAt 2920 .GT,
   pushAt 2921 2 3721,
   opAt 2922 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2923 .POP,
   opAt 2924 .POP,
   opAt 2925 .POP,
   pushAt 2926 2 2080,
   opAt 2927 .MLOAD,
   opAt 2928 (.Dup ⟨1, by decide⟩),
   opAt 2929 .ADD,
   opAt 2930 (.Dup ⟨1, by decide⟩),
   opAt 2931 (.Dup ⟨1, by decide⟩),
   opAt 2932 .LT,
   opAt 2933 (.Swap ⟨1, by decide⟩),
   opAt 2934 .POP,
   opAt 2935 (.Dup ⟨2, by decide⟩),
   opAt 2936 (.Dup ⟨1, by decide⟩),
   opAt 2937 .LT,
   opAt 2938 (.Swap ⟨0, by decide⟩),
   opAt 2939 (.Dup ⟨3, by decide⟩),
   opAt 2940 (.Swap ⟨0, by decide⟩),
   opAt 2941 .SUB,
   opAt 2942 (.Dup ⟨0, by decide⟩),
   pushAt 2943 2 2080,
   opAt 2944 .MSTORE,
   opAt 2945 .POP,
   opAt 2946 .GT,
   opAt 2947 (.Swap ⟨0, by decide⟩),
   opAt 2948 .POP,
   opAt 2949 .ISZERO,
   pushAt 2950 2 3988,
   opAt 2951 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2952 .JUMPDEST,
   pushAt 2953 0 0,
   pushAt 2954 2 2784,
   opAt 2955 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2956 .JUMPDEST,
   opAt 2957 (.Dup ⟨0, by decide⟩),
   opAt 2958 .MLOAD,
   opAt 2959 (.Dup ⟨1, by decide⟩),
   pushAt 2960 2 2112,
   opAt 2961 (.Swap ⟨0, by decide⟩),
   opAt 2962 .SUB,
   opAt 2963 .MLOAD,
   opAt 2964 (.Dup ⟨1, by decide⟩),
   opAt 2965 .ADD,
   opAt 2966 (.Dup ⟨0, by decide⟩),
   opAt 2967 (.Dup ⟨2, by decide⟩),
   opAt 2968 .GT,
   opAt 2969 (.Swap ⟨1, by decide⟩),
   opAt 2970 .POP,
   opAt 2971 (.Dup ⟨3, by decide⟩),
   opAt 2972 .ADD,
   opAt 2973 (.Dup ⟨0, by decide⟩),
   opAt 2974 (.Dup ⟨4, by decide⟩),
   opAt 2975 .GT,
   opAt 2976 (.Swap ⟨3, by decide⟩),
   opAt 2977 .POP,
   opAt 2978 (.Dup ⟨2, by decide⟩),
   opAt 2979 .MSTORE,
   opAt 2980 (.Swap ⟨0, by decide⟩),
   opAt 2981 (.Swap ⟨1, by decide⟩),
   opAt 2982 .OR,
   opAt 2983 (.Swap ⟨0, by decide⟩),
   pushAt 2984 1 31,
   opAt 2985 .NOT,
   opAt 2986 .ADD,
   pushAt 2987 2 2111,
   opAt 2988 (.Dup ⟨1, by decide⟩),
   opAt 2989 .GT,
   pushAt 2990 2 3927,
   opAt 2991 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2992 .POP,
   pushAt 2993 2 2080,
   opAt 2994 .MLOAD,
   opAt 2995 (.Dup ⟨1, by decide⟩),
   opAt 2996 .ADD,
   opAt 2997 (.Dup ⟨0, by decide⟩),
   pushAt 2998 2 2080,
   opAt 2999 .MSTORE,
   opAt 3000 .LT,
   opAt 3001 .ISZERO,
   pushAt 3002 2 3921,
   opAt 3003 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3004 .JUMPDEST,
   pushAt 3005 2 2080,
   opAt 3006 .MLOAD,
   opAt 3007 .ISZERO,
   pushAt 3008 2 4056,
   opAt 3009 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 3010 0 0,
   pushAt 3011 2 2784,
   opAt 3012 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3013 .JUMPDEST,
   opAt 3014 (.Dup ⟨0, by decide⟩),
   opAt 3015 .MLOAD,
   pushAt 3016 2 2112,
   opAt 3017 (.Dup ⟨2, by decide⟩),
   opAt 3018 .SUB,
   opAt 3019 .MLOAD,
   opAt 3020 (.Dup ⟨1, by decide⟩),
   opAt 3021 (.Dup ⟨1, by decide⟩),
   opAt 3022 .GT,
   opAt 3023 (.Swap ⟨1, by decide⟩),
   opAt 3024 .SUB,
   opAt 3025 (.Dup ⟨3, by decide⟩),
   opAt 3026 (.Dup ⟨1, by decide⟩),
   opAt 3027 .LT,
   opAt 3028 (.Swap ⟨0, by decide⟩),
   opAt 3029 (.Dup ⟨4, by decide⟩),
   opAt 3030 (.Swap ⟨0, by decide⟩),
   opAt 3031 .SUB,
   opAt 3032 (.Dup ⟨3, by decide⟩),
   opAt 3033 .MSTORE,
   opAt 3034 .OR,
   opAt 3035 (.Swap ⟨1, by decide⟩),
   opAt 3036 .POP,
   pushAt 3037 1 31,
   opAt 3038 .NOT,
   opAt 3039 .ADD,
   pushAt 3040 2 2111,
   opAt 3041 (.Dup ⟨1, by decide⟩),
   opAt 3042 .GT,
   pushAt 3043 2 4003,
   opAt 3044 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3045 .POP,
   pushAt 3046 2 2080,
   opAt 3047 .MLOAD,
   opAt 3048 .SUB,
   pushAt 3049 2 2080,
   opAt 3050 .MSTORE,
   pushAt 3051 2 3988,
   opAt 3052 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3053 .JUMPDEST,
   pushAt 3054 2 4067,
   pushAt 3055 2 512,
   pushAt 3056 2 4877,
   opAt 3057 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3058 .JUMPDEST,
   pushAt 3059 0 0,
   opAt 3060 .NOT,
   opAt 3061 .ADD,
   pushAt 3062 2 3597,
   opAt 3063 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3064 .JUMPDEST,
   opAt 3065 .POP,
   pushAt 3066 2 2688,
   opAt 3067 .MLOAD,
   pushAt 3068 2 1280,
   pushAt 3069 2 1024,
   opAt 3070 .MCOPY,
   pushAt 3071 2 3216,
   opAt 3072 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3374 = true :=
  Artifact.isValidJumpDest_index 2529 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3418 = true :=
  Artifact.isValidJumpDest_index 2556 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3435 = true :=
  Artifact.isValidJumpDest_index 2564 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3442 = true :=
  Artifact.isValidJumpDest_index 2568 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3473 = true :=
  Artifact.isValidJumpDest_index 2592 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3597 = true :=
  Artifact.isValidJumpDest_index 2687 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3721 = true :=
  Artifact.isValidJumpDest_index 2770 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3921 = true :=
  Artifact.isValidJumpDest_index 2952 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3927 = true :=
  Artifact.isValidJumpDest_index 2956 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3988 = true :=
  Artifact.isValidJumpDest_index 3004 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4003 = true :=
  Artifact.isValidJumpDest_index 3013 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4056 = true :=
  Artifact.isValidJumpDest_index 3053 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4067 = true :=
  Artifact.isValidJumpDest_index 3058 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4075 = true :=
  Artifact.isValidJumpDest_index 3064 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
