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
  [opAt 2530 .JUMPDEST,
   opAt 2531 (.Dup ⟨0, by decide⟩),
   opAt 2532 (.Dup ⟨3, by decide⟩),
   opAt 2533 .EQ,
   pushAt 2534 0 0,
   opAt 2535 .MLOAD,
   pushAt 2536 1 255,
   opAt 2537 .SHR,
   opAt 2538 .AND,
   opAt 2539 .ISZERO,
   pushAt 2540 2 3352,
   opAt 2541 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2542 (.Dup ⟨0, by decide⟩),
   pushAt 2543 1 96,
   pushAt 2544 2 1024,
   opAt 2545 .CALLDATACOPY,
   opAt 2546 (.Dup ⟨0, by decide⟩),
   pushAt 2547 1 96,
   pushAt 2548 2 8256,
   opAt 2549 .CALLDATACOPY,
   pushAt 2550 0 0,
   pushAt 2551 2 8224,
   opAt 2552 .MSTORE,
   pushAt 2553 2 3357,
   pushAt 2554 2 2048,
   pushAt 2555 2 4642,
   opAt 2556 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2557 .JUMPDEST,
   pushAt 2558 2 1312,
   opAt 2559 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2560 .JUMPDEST,
   pushAt 2561 1 1,
   pushAt 2562 2 9408,
   opAt 2563 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2564 .JUMPDEST,
   opAt 2565 (.Dup ⟨0, by decide⟩),
   opAt 2566 .MLOAD,
   opAt 2567 .NOT,
   opAt 2568 (.Dup ⟨2, by decide⟩),
   opAt 2569 .ADD,
   opAt 2570 (.Dup ⟨2, by decide⟩),
   opAt 2571 (.Dup ⟨1, by decide⟩),
   opAt 2572 .LT,
   opAt 2573 (.Swap ⟨2, by decide⟩),
   opAt 2574 .POP,
   opAt 2575 (.Dup ⟨1, by decide⟩),
   pushAt 2576 2 5120,
   opAt 2577 .ADD,
   opAt 2578 .MSTORE,
   opAt 2579 (.Dup ⟨0, by decide⟩),
   opAt 2580 .ISZERO,
   pushAt 2581 2 3395,
   opAt 2582 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2583 1 31,
   opAt 2584 .NOT,
   opAt 2585 .ADD,
   pushAt 2586 2 3364,
   opAt 2587 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2588 .JUMPDEST,
   opAt 2589 .POP,
   opAt 2590 .POP,
   pushAt 2591 0 0,
   opAt 2592 .MLOAD,
   opAt 2593 (.Dup ⟨0, by decide⟩),
   pushAt 2594 0 0,
   opAt 2595 .SUB,
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 .AND,
   opAt 2598 (.Dup ⟨0, by decide⟩),
   pushAt 2599 2 6144,
   opAt 2600 .MSTORE,
   opAt 2601 (.Dup ⟨0, by decide⟩),
   opAt 2602 (.Dup ⟨2, by decide⟩),
   opAt 2603 .DIV,
   opAt 2604 (.Dup ⟨0, by decide⟩),
   pushAt 2605 2 6176,
   opAt 2606 .MSTORE,
   opAt 2607 (.Dup ⟨1, by decide⟩),
   pushAt 2608 0 0,
   opAt 2609 .SUB,
   opAt 2610 (.Dup ⟨2, by decide⟩),
   opAt 2611 (.Swap ⟨0, by decide⟩),
   opAt 2612 .DIV,
   pushAt 2613 1 1,
   opAt 2614 .ADD,
   pushAt 2615 2 6208,
   opAt 2616 .MSTORE,
   opAt 2617 (.Dup ⟨0, by decide⟩),
   pushAt 2618 0 0,
   opAt 2619 .SUB,
   opAt 2620 (.Dup ⟨1, by decide⟩),
   opAt 2621 (.Swap ⟨0, by decide⟩),
   opAt 2622 .MOD,
   pushAt 2623 2 6240,
   opAt 2624 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2625 (.Dup ⟨0, by decide⟩),
   pushAt 2626 1 2,
   opAt 2627 .SUB,
   opAt 2628 (.Dup ⟨0, by decide⟩),
   opAt 2629 (.Dup ⟨2, by decide⟩),
   opAt 2630 .MUL,
   pushAt 2631 1 2,
   opAt 2632 .SUB,
   opAt 2633 .MUL,
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
   opAt 2645 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2646 (.Dup ⟨0, by decide⟩),
   opAt 2647 (.Dup ⟨2, by decide⟩),
   opAt 2648 .MUL,
   pushAt 2649 1 2,
   opAt 2650 .SUB,
   opAt 2651 .MUL,
   opAt 2652 (.Dup ⟨0, by decide⟩),
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
   pushAt 2670 2 6272,
   opAt 2671 .MSTORE,
   opAt 2672 .POP,
   opAt 2673 .POP,
   opAt 2674 .POP,
   opAt 2675 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2676 .JUMPDEST,
   opAt 2677 (.Dup ⟨0, by decide⟩),
   opAt 2678 .ISZERO,
   pushAt 2679 2 3889,
   opAt 2680 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2681 (.Dup ⟨1, by decide⟩),
   pushAt 2682 2 2048,
   pushAt 2683 2 8224,
   opAt 2684 .MCOPY,
   pushAt 2685 0 0,
   pushAt 2686 2 9440,
   opAt 2687 .MLOAD,
   opAt 2688 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2689 2 2048,
   opAt 2690 .MLOAD,
   pushAt 2691 2 6144,
   opAt 2692 .MLOAD,
   opAt 2693 (.Dup ⟨0, by decide⟩),
   opAt 2694 (.Dup ⟨2, by decide⟩),
   opAt 2695 .DIV,
   opAt 2696 (.Swap ⟨1, by decide⟩),
   opAt 2697 .MOD,
   pushAt 2698 2 6208,
   opAt 2699 .MLOAD,
   opAt 2700 .MUL,
   pushAt 2701 2 2080,
   opAt 2702 .MLOAD,
   pushAt 2703 2 6144,
   opAt 2704 .MLOAD,
   opAt 2705 (.Swap ⟨0, by decide⟩),
   opAt 2706 .DIV,
   opAt 2707 .ADD,
   pushAt 2708 2 6176,
   opAt 2709 .MLOAD,
   opAt 2710 (.Dup ⟨0, by decide⟩),
   pushAt 2711 2 6240,
   opAt 2712 .MLOAD,
   opAt 2713 (.Dup ⟨4, by decide⟩),
   opAt 2714 .MULMOD,
   opAt 2715 (.Dup ⟨2, by decide⟩),
   opAt 2716 .ADDMOD,
   opAt 2717 (.Swap ⟨0, by decide⟩),
   opAt 2718 .SUB,
   pushAt 2719 2 6272,
   opAt 2720 .MLOAD,
   opAt 2721 .MUL,
   opAt 2722 (.Dup ⟨0, by decide⟩),
   pushAt 2723 0 0,
   opAt 2724 .MLOAD,
   opAt 2725 .MUL,
   pushAt 2726 2 2080,
   opAt 2727 .MLOAD,
   opAt 2728 .SUB,
   pushAt 2729 1 32,
   opAt 2730 .MLOAD,
   pushAt 2731 1 128,
   opAt 2732 .SHR,
   opAt 2733 (.Dup ⟨2, by decide⟩),
   pushAt 2734 1 128,
   opAt 2735 .SHR,
   opAt 2736 .MUL,
   opAt 2737 .GT,
   opAt 2738 (.Swap ⟨0, by decide⟩),
   opAt 2739 .SUB,
   opAt 2740 (.Swap ⟨0, by decide⟩),
   pushAt 2741 2 6176,
   opAt 2742 .MLOAD,
   opAt 2743 .GT,
   opAt 2744 .ISZERO,
   pushAt 2745 0 0,
   opAt 2746 .SUB,
   opAt 2747 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2748 0 0,
   pushAt 2749 2 9440,
   opAt 2750 .MLOAD,
   pushAt 2751 2 9408,
   opAt 2752 .MLOAD,
   pushAt 2753 2 5120,
   opAt 2754 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2755 .JUMPDEST,
   opAt 2756 (.Dup ⟨0, by decide⟩),
   opAt 2757 .MLOAD,
   pushAt 2758 0 0,
   opAt 2759 .NOT,
   opAt 2760 (.Dup ⟨5, by decide⟩),
   opAt 2761 (.Dup ⟨2, by decide⟩),
   opAt 2762 .MUL,
   opAt 2763 (.Swap ⟨1, by decide⟩),
   opAt 2764 (.Dup ⟨6, by decide⟩),
   opAt 2765 .MULMOD,
   opAt 2766 (.Dup ⟨1, by decide⟩),
   opAt 2767 (.Dup ⟨1, by decide⟩),
   opAt 2768 .LT,
   opAt 2769 .SUB,
   opAt 2770 (.Dup ⟨4, by decide⟩),
   opAt 2771 (.Dup ⟨2, by decide⟩),
   opAt 2772 .ADD,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   opAt 2774 (.Swap ⟨5, by decide⟩),
   opAt 2775 .GT,
   opAt 2776 .SUB,
   opAt 2777 .SUB,
   opAt 2778 (.Dup ⟨3, by decide⟩),
   opAt 2779 (.Dup ⟨3, by decide⟩),
   opAt 2780 .MLOAD,
   opAt 2781 .ADD,
   opAt 2782 (.Dup ⟨0, by decide⟩),
   opAt 2783 (.Swap ⟨4, by decide⟩),
   opAt 2784 .GT,
   opAt 2785 .ADD,
   opAt 2786 (.Swap ⟨2, by decide⟩),
   opAt 2787 (.Dup ⟨2, by decide⟩),
   pushAt 2788 1 31,
   opAt 2789 .NOT,
   opAt 2790 .ADD,
   opAt 2791 (.Swap ⟨2, by decide⟩),
   opAt 2792 .MSTORE,
   pushAt 2793 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2794 .ADD,
   pushAt 2795 2 8224,
   opAt 2796 (.Dup ⟨2, by decide⟩),
   opAt 2797 .GT,
   pushAt 2798 2 3618,
   opAt 2799 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2800 .POP,
   opAt 2801 .POP,
   pushAt 2802 2 8224,
   opAt 2803 .MLOAD,
   opAt 2804 (.Dup ⟨1, by decide⟩),
   opAt 2805 .ADD,
   opAt 2806 (.Dup ⟨1, by decide⟩),
   opAt 2807 (.Dup ⟨1, by decide⟩),
   opAt 2808 .LT,
   opAt 2809 (.Swap ⟨1, by decide⟩),
   opAt 2810 .POP,
   opAt 2811 (.Dup ⟨2, by decide⟩),
   opAt 2812 (.Dup ⟨1, by decide⟩),
   opAt 2813 .LT,
   opAt 2814 (.Swap ⟨0, by decide⟩),
   opAt 2815 (.Dup ⟨3, by decide⟩),
   opAt 2816 (.Swap ⟨0, by decide⟩),
   opAt 2817 .SUB,
   opAt 2818 (.Dup ⟨0, by decide⟩),
   pushAt 2819 2 8224,
   opAt 2820 .MSTORE,
   opAt 2821 .POP,
   opAt 2822 .GT,
   opAt 2823 (.Swap ⟨0, by decide⟩),
   opAt 2824 .POP,
   opAt 2825 .ISZERO,
   pushAt 2826 2 3801,
   opAt 2827 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2828 .JUMPDEST,
   pushAt 2829 0 0,
   pushAt 2830 2 9440,
   opAt 2831 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2832 .JUMPDEST,
   opAt 2833 (.Dup ⟨0, by decide⟩),
   opAt 2834 .MLOAD,
   opAt 2835 (.Dup ⟨1, by decide⟩),
   pushAt 2836 2 8256,
   opAt 2837 (.Swap ⟨0, by decide⟩),
   opAt 2838 .SUB,
   opAt 2839 .MLOAD,
   opAt 2840 (.Dup ⟨1, by decide⟩),
   opAt 2841 .ADD,
   opAt 2842 (.Dup ⟨0, by decide⟩),
   opAt 2843 (.Dup ⟨2, by decide⟩),
   opAt 2844 .GT,
   opAt 2845 (.Swap ⟨1, by decide⟩),
   opAt 2846 .POP,
   opAt 2847 (.Dup ⟨3, by decide⟩),
   opAt 2848 .ADD,
   opAt 2849 (.Dup ⟨0, by decide⟩),
   opAt 2850 (.Dup ⟨4, by decide⟩),
   opAt 2851 .GT,
   opAt 2852 (.Swap ⟨3, by decide⟩),
   opAt 2853 .POP,
   opAt 2854 (.Dup ⟨2, by decide⟩),
   opAt 2855 .MSTORE,
   opAt 2856 (.Swap ⟨0, by decide⟩),
   opAt 2857 (.Swap ⟨1, by decide⟩),
   opAt 2858 .OR,
   opAt 2859 (.Swap ⟨0, by decide⟩),
   pushAt 2860 1 31,
   opAt 2861 .NOT,
   opAt 2862 .ADD,
   pushAt 2863 2 8255,
   opAt 2864 (.Dup ⟨1, by decide⟩),
   opAt 2865 .GT,
   pushAt 2866 2 3740,
   opAt 2867 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2868 .POP,
   pushAt 2869 2 8224,
   opAt 2870 .MLOAD,
   opAt 2871 (.Dup ⟨1, by decide⟩),
   opAt 2872 .ADD,
   opAt 2873 (.Dup ⟨0, by decide⟩),
   pushAt 2874 2 8224,
   opAt 2875 .MSTORE,
   opAt 2876 .LT,
   opAt 2877 .ISZERO,
   pushAt 2878 2 3734,
   opAt 2879 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2880 .JUMPDEST,
   pushAt 2881 2 8224,
   opAt 2882 .MLOAD,
   opAt 2883 .ISZERO,
   pushAt 2884 2 3869,
   opAt 2885 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2886 0 0,
   pushAt 2887 2 9440,
   opAt 2888 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2889 .JUMPDEST,
   opAt 2890 (.Dup ⟨0, by decide⟩),
   opAt 2891 .MLOAD,
   pushAt 2892 2 8256,
   opAt 2893 (.Dup ⟨2, by decide⟩),
   opAt 2894 .SUB,
   opAt 2895 .MLOAD,
   opAt 2896 (.Dup ⟨1, by decide⟩),
   opAt 2897 (.Dup ⟨1, by decide⟩),
   opAt 2898 .GT,
   opAt 2899 (.Swap ⟨1, by decide⟩),
   opAt 2900 .SUB,
   opAt 2901 (.Dup ⟨3, by decide⟩),
   opAt 2902 (.Dup ⟨1, by decide⟩),
   opAt 2903 .LT,
   opAt 2904 (.Swap ⟨0, by decide⟩),
   opAt 2905 (.Dup ⟨4, by decide⟩),
   opAt 2906 (.Swap ⟨0, by decide⟩),
   opAt 2907 .SUB,
   opAt 2908 (.Dup ⟨3, by decide⟩),
   opAt 2909 .MSTORE,
   opAt 2910 .OR,
   opAt 2911 (.Swap ⟨1, by decide⟩),
   opAt 2912 .POP,
   pushAt 2913 1 31,
   opAt 2914 .NOT,
   opAt 2915 .ADD,
   pushAt 2916 2 8255,
   opAt 2917 (.Dup ⟨1, by decide⟩),
   opAt 2918 .GT,
   pushAt 2919 2 3816,
   opAt 2920 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2921 .POP,
   pushAt 2922 2 8224,
   opAt 2923 .MLOAD,
   opAt 2924 .SUB,
   pushAt 2925 2 8224,
   opAt 2926 .MSTORE,
   pushAt 2927 2 3801,
   opAt 2928 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2929 .JUMPDEST,
   pushAt 2930 2 3880,
   pushAt 2931 2 2048,
   pushAt 2932 2 4642,
   opAt 2933 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2934 .JUMPDEST,
   pushAt 2935 1 1,
   opAt 2936 (.Swap ⟨0, by decide⟩),
   opAt 2937 .SUB,
   pushAt 2938 2 3502,
   opAt 2939 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2940 .JUMPDEST,
   opAt 2941 .POP,
   pushAt 2942 2 3150,
   opAt 2943 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3308 = true :=
  Artifact.isValidJumpDest_index 2530 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3352 = true :=
  Artifact.isValidJumpDest_index 2557 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3357 = true :=
  Artifact.isValidJumpDest_index 2560 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3364 = true :=
  Artifact.isValidJumpDest_index 2564 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3395 = true :=
  Artifact.isValidJumpDest_index 2588 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3502 = true :=
  Artifact.isValidJumpDest_index 2676 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3618 = true :=
  Artifact.isValidJumpDest_index 2755 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3734 = true :=
  Artifact.isValidJumpDest_index 2828 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3740 = true :=
  Artifact.isValidJumpDest_index 2832 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3801 = true :=
  Artifact.isValidJumpDest_index 2880 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3816 = true :=
  Artifact.isValidJumpDest_index 2889 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3869 = true :=
  Artifact.isValidJumpDest_index 2929 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3880 = true :=
  Artifact.isValidJumpDest_index 2934 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3889 = true :=
  Artifact.isValidJumpDest_index 2940 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
