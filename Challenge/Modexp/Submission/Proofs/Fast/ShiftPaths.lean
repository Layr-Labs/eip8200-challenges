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
   pushAt 2560 2 4871,
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
   pushAt 2698 2 4069,
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
   pushAt 2938 2 3717,
   opAt 2939 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2940 .POP,
   opAt 2941 .POP,
   opAt 2942 .POP,
   pushAt 2943 2 2080,
   opAt 2944 .MLOAD,
   opAt 2945 (.Dup ⟨1, by decide⟩),
   opAt 2946 .ADD,
   opAt 2947 (.Dup ⟨0, by decide⟩),
   opAt 2948 (.Swap ⟨1, by decide⟩),
   opAt 2949 .GT,
   opAt 2950 (.Dup ⟨1, by decide⟩),
   opAt 2951 (.Dup ⟨3, by decide⟩),
   opAt 2952 .GT,
   opAt 2953 .GT,
   opAt 2954 (.Swap ⟨1, by decide⟩),
   opAt 2955 (.Swap ⟨0, by decide⟩),
   opAt 2956 .SUB,
   opAt 2957 (.Dup ⟨0, by decide⟩),
   pushAt 2958 2 2080,
   opAt 2959 .MSTORE,
   opAt 2960 (.Dup ⟨1, by decide⟩),
   opAt 2961 .OR,
   pushAt 2962 2 3925,
   opAt 2963 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2971 .JUMPDEST,
   opAt 2972 .ISZERO,
   pushAt 2973 2 4010,
   opAt 2974 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2975 .JUMPDEST,
   pushAt 2976 0 0,
   pushAt 2977 2 2784,
   opAt 2978 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2979 .JUMPDEST,
   opAt 2980 (.Dup ⟨0, by decide⟩),
   opAt 2981 .MLOAD,
   opAt 2982 (.Dup ⟨1, by decide⟩),
   pushAt 2983 2 2112,
   opAt 2984 (.Swap ⟨0, by decide⟩),
   opAt 2985 .SUB,
   opAt 2986 .MLOAD,
   opAt 2987 (.Dup ⟨1, by decide⟩),
   opAt 2988 .ADD,
   opAt 2989 (.Dup ⟨0, by decide⟩),
   opAt 2990 (.Dup ⟨2, by decide⟩),
   opAt 2991 .GT,
   opAt 2992 (.Swap ⟨1, by decide⟩),
   opAt 2993 .POP,
   opAt 2994 (.Dup ⟨3, by decide⟩),
   opAt 2995 .ADD,
   opAt 2996 (.Dup ⟨0, by decide⟩),
   opAt 2997 (.Dup ⟨4, by decide⟩),
   opAt 2998 .GT,
   opAt 2999 (.Swap ⟨3, by decide⟩),
   opAt 3000 .POP,
   opAt 3001 (.Dup ⟨2, by decide⟩),
   opAt 3002 .MSTORE,
   opAt 3003 (.Swap ⟨0, by decide⟩),
   opAt 3004 (.Swap ⟨1, by decide⟩),
   opAt 3005 .OR,
   opAt 3006 (.Swap ⟨0, by decide⟩),
   pushAt 3007 1 31,
   opAt 3008 .NOT,
   opAt 3009 .ADD,
   pushAt 3010 2 2111,
   opAt 3011 (.Dup ⟨1, by decide⟩),
   opAt 3012 .GT,
   pushAt 3013 2 3937,
   opAt 3014 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3015 .POP,
   pushAt 3016 2 2080,
   opAt 3017 .MLOAD,
   opAt 3018 (.Dup ⟨1, by decide⟩),
   opAt 3019 .ADD,
   opAt 3020 (.Dup ⟨0, by decide⟩),
   pushAt 3021 2 2080,
   opAt 3022 .MSTORE,
   opAt 3023 .LT,
   opAt 3024 .ISZERO,
   pushAt 3025 2 3931,
   opAt 3026 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3027 .JUMPDEST,
   pushAt 3028 2 2080,
   opAt 3029 .MLOAD,
   opAt 3030 (.Dup ⟨0, by decide⟩),
   opAt 3031 .ISZERO,
   pushAt 3032 2 3912,
   opAt 3033 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3027 .JUMPDEST,
   pushAt 3028 2 2080,
   opAt 3029 .MLOAD,
   opAt 3030 (.Dup ⟨0, by decide⟩),
   opAt 3031 .ISZERO,
   pushAt 3032 2 3912,
   opAt 3033 .JUMPI,
   opAt 3034 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3035 .JUMPDEST,
   pushAt 3036 0 0,
   pushAt 3037 2 2784,
   opAt 3038 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3039 .JUMPDEST,
   opAt 3040 (.Dup ⟨0, by decide⟩),
   opAt 3041 .MLOAD,
   pushAt 3042 2 2112,
   opAt 3043 (.Dup ⟨2, by decide⟩),
   opAt 3044 .SUB,
   opAt 3045 .MLOAD,
   opAt 3046 (.Dup ⟨1, by decide⟩),
   opAt 3047 (.Dup ⟨1, by decide⟩),
   opAt 3048 .GT,
   opAt 3049 (.Swap ⟨1, by decide⟩),
   opAt 3050 .SUB,
   opAt 3051 (.Dup ⟨3, by decide⟩),
   opAt 3052 (.Dup ⟨1, by decide⟩),
   opAt 3053 .LT,
   opAt 3054 (.Swap ⟨0, by decide⟩),
   opAt 3055 (.Dup ⟨4, by decide⟩),
   opAt 3056 (.Swap ⟨0, by decide⟩),
   opAt 3057 .SUB,
   opAt 3058 (.Dup ⟨3, by decide⟩),
   opAt 3059 .MSTORE,
   opAt 3060 .OR,
   opAt 3061 (.Swap ⟨1, by decide⟩),
   opAt 3062 .POP,
   pushAt 3063 1 31,
   opAt 3064 .NOT,
   opAt 3065 .ADD,
   pushAt 3066 2 2111,
   opAt 3067 (.Dup ⟨1, by decide⟩),
   opAt 3068 .GT,
   pushAt 3069 2 4016,
   opAt 3070 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3071 .POP,
   pushAt 3072 2 2080,
   opAt 3073 .MLOAD,
   opAt 3074 .SUB,
   pushAt 3075 2 2080,
   opAt 3076 .MSTORE,
   pushAt 3077 2 3998,
   opAt 3078 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2964 .JUMPDEST,
   opAt 2965 .NOT,
   opAt 2966 .ADD,
   pushAt 2967 2 3593,
   pushAt 2968 2 512,
   pushAt 2969 2 4871,
   opAt 2970 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3079 .JUMPDEST,
   opAt 3080 .POP,
   pushAt 3081 2 2688,
   opAt 3082 .MLOAD,
   pushAt 3083 2 1280,
   pushAt 3084 2 1024,
   opAt 3085 .MCOPY,
   pushAt 3086 2 3216,
   opAt 3087 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3469 = true :=
  Artifact.isValidJumpDest_index 2596 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3593 = true :=
  Artifact.isValidJumpDest_index 2695 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3717 = true :=
  Artifact.isValidJumpDest_index 2779 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3931 = true :=
  Artifact.isValidJumpDest_index 2975 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3937 = true :=
  Artifact.isValidJumpDest_index 2979 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3998 = true :=
  Artifact.isValidJumpDest_index 3027 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4016 = true :=
  Artifact.isValidJumpDest_index 3039 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3925 = true :=
  Artifact.isValidJumpDest_index 2971 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4010 = true :=
  Artifact.isValidJumpDest_index 3035 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3912 = true :=
  Artifact.isValidJumpDest_index 2964 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4069 = true :=
  Artifact.isValidJumpDest_index 3079 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
