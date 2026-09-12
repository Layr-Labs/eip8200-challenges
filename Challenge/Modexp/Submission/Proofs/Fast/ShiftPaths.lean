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
  [opAt 2523 .JUMPDEST,
   opAt 2524 (.Dup ⟨0, by decide⟩),
   opAt 2525 (.Dup ⟨3, by decide⟩),
   opAt 2526 .EQ,
   pushAt 2527 0 0,
   opAt 2528 .MLOAD,
   pushAt 2529 1 255,
   opAt 2530 .SHR,
   opAt 2531 .AND,
   opAt 2532 .ISZERO,
   pushAt 2533 2 3334,
   opAt 2534 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2535 (.Dup ⟨0, by decide⟩),
   pushAt 2536 1 96,
   pushAt 2537 2 1024,
   opAt 2538 .CALLDATACOPY,
   opAt 2539 (.Dup ⟨0, by decide⟩),
   pushAt 2540 1 96,
   pushAt 2541 2 8256,
   opAt 2542 .CALLDATACOPY,
   pushAt 2543 0 0,
   pushAt 2544 2 8224,
   opAt 2545 .MSTORE,
   pushAt 2546 2 3351,
   pushAt 2547 2 2048,
   pushAt 2548 2 4653,
   opAt 2549 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2550 .JUMPDEST,
   pushAt 2551 1 1,
   pushAt 2552 2 4096,
   opAt 2553 .MSTORE,
   pushAt 2554 2 1296,
   pushAt 2555 2 4096,
   pushAt 2556 2 2077,
   opAt 2557 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2558 .JUMPDEST,
   pushAt 2559 1 1,
   pushAt 2560 2 9408,
   opAt 2561 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2562 .JUMPDEST,
   opAt 2563 (.Dup ⟨0, by decide⟩),
   opAt 2564 .MLOAD,
   opAt 2565 .NOT,
   opAt 2566 (.Dup ⟨2, by decide⟩),
   opAt 2567 .ADD,
   opAt 2568 (.Dup ⟨2, by decide⟩),
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .LT,
   opAt 2571 (.Swap ⟨2, by decide⟩),
   opAt 2572 .POP,
   opAt 2573 (.Dup ⟨1, by decide⟩),
   pushAt 2574 2 5120,
   opAt 2575 .ADD,
   opAt 2576 .MSTORE,
   opAt 2577 (.Dup ⟨0, by decide⟩),
   opAt 2578 .ISZERO,
   pushAt 2579 2 3389,
   opAt 2580 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2581 1 31,
   opAt 2582 .NOT,
   opAt 2583 .ADD,
   pushAt 2584 2 3358,
   opAt 2585 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2586 .JUMPDEST,
   opAt 2587 .POP,
   opAt 2588 .POP,
   pushAt 2589 0 0,
   opAt 2590 .MLOAD,
   opAt 2591 (.Dup ⟨0, by decide⟩),
   pushAt 2592 0 0,
   opAt 2593 .SUB,
   opAt 2594 (.Dup ⟨1, by decide⟩),
   opAt 2595 .AND,
   opAt 2596 (.Dup ⟨0, by decide⟩),
   pushAt 2597 2 6144,
   opAt 2598 .MSTORE,
   opAt 2599 (.Dup ⟨0, by decide⟩),
   opAt 2600 (.Dup ⟨2, by decide⟩),
   opAt 2601 .DIV,
   opAt 2602 (.Dup ⟨0, by decide⟩),
   pushAt 2603 2 6176,
   opAt 2604 .MSTORE,
   opAt 2605 (.Dup ⟨1, by decide⟩),
   pushAt 2606 0 0,
   opAt 2607 .SUB,
   opAt 2608 (.Dup ⟨2, by decide⟩),
   opAt 2609 (.Swap ⟨0, by decide⟩),
   opAt 2610 .DIV,
   pushAt 2611 1 1,
   opAt 2612 .ADD,
   pushAt 2613 2 6208,
   opAt 2614 .MSTORE,
   opAt 2615 (.Dup ⟨0, by decide⟩),
   pushAt 2616 0 0,
   opAt 2617 .SUB,
   opAt 2618 (.Dup ⟨1, by decide⟩),
   opAt 2619 (.Swap ⟨0, by decide⟩),
   opAt 2620 .MOD,
   pushAt 2621 2 6240,
   opAt 2622 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2623 (.Dup ⟨0, by decide⟩),
   pushAt 2624 1 2,
   opAt 2625 .SUB,
   opAt 2626 (.Dup ⟨0, by decide⟩),
   opAt 2627 (.Dup ⟨2, by decide⟩),
   opAt 2628 .MUL,
   pushAt 2629 1 2,
   opAt 2630 .SUB,
   opAt 2631 .MUL,
   opAt 2632 (.Dup ⟨0, by decide⟩),
   opAt 2633 (.Dup ⟨2, by decide⟩),
   opAt 2634 .MUL,
   pushAt 2635 1 2,
   opAt 2636 .SUB,
   opAt 2637 .MUL,
   opAt 2638 (.Dup ⟨0, by decide⟩),
   opAt 2639 (.Dup ⟨2, by decide⟩),
   opAt 2640 .MUL,
   pushAt 2641 1 2,
   opAt 2642 .SUB,
   opAt 2643 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2644 (.Dup ⟨0, by decide⟩),
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
   opAt 2655 .MUL,
   opAt 2656 (.Dup ⟨0, by decide⟩),
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
   pushAt 2668 2 6272,
   opAt 2669 .MSTORE,
   opAt 2670 .POP,
   opAt 2671 .POP,
   opAt 2672 .POP,
   opAt 2673 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2674 .JUMPDEST,
   opAt 2675 (.Dup ⟨0, by decide⟩),
   opAt 2676 .ISZERO,
   pushAt 2677 2 3883,
   opAt 2678 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2679 (.Dup ⟨1, by decide⟩),
   pushAt 2680 2 2048,
   pushAt 2681 2 8224,
   opAt 2682 .MCOPY,
   pushAt 2683 0 0,
   pushAt 2684 2 9440,
   opAt 2685 .MLOAD,
   opAt 2686 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2687 2 2048,
   opAt 2688 .MLOAD,
   pushAt 2689 2 6144,
   opAt 2690 .MLOAD,
   opAt 2691 (.Dup ⟨0, by decide⟩),
   opAt 2692 (.Dup ⟨2, by decide⟩),
   opAt 2693 .DIV,
   opAt 2694 (.Swap ⟨1, by decide⟩),
   opAt 2695 .MOD,
   pushAt 2696 2 6208,
   opAt 2697 .MLOAD,
   opAt 2698 .MUL,
   pushAt 2699 2 2080,
   opAt 2700 .MLOAD,
   pushAt 2701 2 6144,
   opAt 2702 .MLOAD,
   opAt 2703 (.Swap ⟨0, by decide⟩),
   opAt 2704 .DIV,
   opAt 2705 .ADD,
   pushAt 2706 2 6176,
   opAt 2707 .MLOAD,
   opAt 2708 (.Dup ⟨0, by decide⟩),
   pushAt 2709 2 6240,
   opAt 2710 .MLOAD,
   opAt 2711 (.Dup ⟨4, by decide⟩),
   opAt 2712 .MULMOD,
   opAt 2713 (.Dup ⟨2, by decide⟩),
   opAt 2714 .ADDMOD,
   opAt 2715 (.Swap ⟨0, by decide⟩),
   opAt 2716 .SUB,
   pushAt 2717 2 6272,
   opAt 2718 .MLOAD,
   opAt 2719 .MUL,
   opAt 2720 (.Dup ⟨0, by decide⟩),
   pushAt 2721 0 0,
   opAt 2722 .MLOAD,
   opAt 2723 .MUL,
   pushAt 2724 2 2080,
   opAt 2725 .MLOAD,
   opAt 2726 .SUB,
   pushAt 2727 1 32,
   opAt 2728 .MLOAD,
   pushAt 2729 1 128,
   opAt 2730 .SHR,
   opAt 2731 (.Dup ⟨2, by decide⟩),
   pushAt 2732 1 128,
   opAt 2733 .SHR,
   opAt 2734 .MUL,
   opAt 2735 .GT,
   opAt 2736 (.Swap ⟨0, by decide⟩),
   opAt 2737 .SUB,
   opAt 2738 (.Swap ⟨0, by decide⟩),
   pushAt 2739 2 6176,
   opAt 2740 .MLOAD,
   opAt 2741 .GT,
   opAt 2742 .ISZERO,
   pushAt 2743 0 0,
   opAt 2744 .SUB,
   opAt 2745 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2746 0 0,
   pushAt 2747 2 9440,
   opAt 2748 .MLOAD,
   pushAt 2749 2 9408,
   opAt 2750 .MLOAD,
   pushAt 2751 2 5120,
   opAt 2752 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2753 .JUMPDEST,
   opAt 2754 (.Dup ⟨0, by decide⟩),
   opAt 2755 .MLOAD,
   pushAt 2756 0 0,
   opAt 2757 .NOT,
   opAt 2758 (.Dup ⟨5, by decide⟩),
   opAt 2759 (.Dup ⟨2, by decide⟩),
   opAt 2760 .MUL,
   opAt 2761 (.Swap ⟨1, by decide⟩),
   opAt 2762 (.Dup ⟨6, by decide⟩),
   opAt 2763 .MULMOD,
   opAt 2764 (.Dup ⟨1, by decide⟩),
   opAt 2765 (.Dup ⟨1, by decide⟩),
   opAt 2766 .LT,
   opAt 2767 .SUB,
   opAt 2768 (.Dup ⟨4, by decide⟩),
   opAt 2769 (.Dup ⟨2, by decide⟩),
   opAt 2770 .ADD,
   opAt 2771 (.Dup ⟨0, by decide⟩),
   opAt 2772 (.Swap ⟨5, by decide⟩),
   opAt 2773 .GT,
   opAt 2774 .SUB,
   opAt 2775 .SUB,
   opAt 2776 (.Dup ⟨3, by decide⟩),
   opAt 2777 (.Dup ⟨3, by decide⟩),
   opAt 2778 .MLOAD,
   opAt 2779 .ADD,
   opAt 2780 (.Dup ⟨0, by decide⟩),
   opAt 2781 (.Swap ⟨4, by decide⟩),
   opAt 2782 .GT,
   opAt 2783 .ADD,
   opAt 2784 (.Swap ⟨2, by decide⟩),
   opAt 2785 (.Dup ⟨2, by decide⟩),
   pushAt 2786 1 31,
   opAt 2787 .NOT,
   opAt 2788 .ADD,
   opAt 2789 (.Swap ⟨2, by decide⟩),
   opAt 2790 .MSTORE,
   pushAt 2791 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2792 .ADD,
   pushAt 2793 2 8224,
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .GT,
   pushAt 2796 2 3612,
   opAt 2797 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2798 .POP,
   opAt 2799 .POP,
   pushAt 2800 2 8224,
   opAt 2801 .MLOAD,
   opAt 2802 (.Dup ⟨1, by decide⟩),
   opAt 2803 .ADD,
   opAt 2804 (.Dup ⟨1, by decide⟩),
   opAt 2805 (.Dup ⟨1, by decide⟩),
   opAt 2806 .LT,
   opAt 2807 (.Swap ⟨1, by decide⟩),
   opAt 2808 .POP,
   opAt 2809 (.Dup ⟨2, by decide⟩),
   opAt 2810 (.Dup ⟨1, by decide⟩),
   opAt 2811 .LT,
   opAt 2812 (.Swap ⟨0, by decide⟩),
   opAt 2813 (.Dup ⟨3, by decide⟩),
   opAt 2814 (.Swap ⟨0, by decide⟩),
   opAt 2815 .SUB,
   opAt 2816 (.Dup ⟨0, by decide⟩),
   pushAt 2817 2 8224,
   opAt 2818 .MSTORE,
   opAt 2819 .POP,
   opAt 2820 .GT,
   opAt 2821 (.Swap ⟨0, by decide⟩),
   opAt 2822 .POP,
   opAt 2823 .ISZERO,
   pushAt 2824 2 3795,
   opAt 2825 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2826 .JUMPDEST,
   pushAt 2827 0 0,
   pushAt 2828 2 9440,
   opAt 2829 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2830 .JUMPDEST,
   opAt 2831 (.Dup ⟨0, by decide⟩),
   opAt 2832 .MLOAD,
   opAt 2833 (.Dup ⟨1, by decide⟩),
   pushAt 2834 2 8256,
   opAt 2835 (.Swap ⟨0, by decide⟩),
   opAt 2836 .SUB,
   opAt 2837 .MLOAD,
   opAt 2838 (.Dup ⟨1, by decide⟩),
   opAt 2839 .ADD,
   opAt 2840 (.Dup ⟨0, by decide⟩),
   opAt 2841 (.Dup ⟨2, by decide⟩),
   opAt 2842 .GT,
   opAt 2843 (.Swap ⟨1, by decide⟩),
   opAt 2844 .POP,
   opAt 2845 (.Dup ⟨3, by decide⟩),
   opAt 2846 .ADD,
   opAt 2847 (.Dup ⟨0, by decide⟩),
   opAt 2848 (.Dup ⟨4, by decide⟩),
   opAt 2849 .GT,
   opAt 2850 (.Swap ⟨3, by decide⟩),
   opAt 2851 .POP,
   opAt 2852 (.Dup ⟨2, by decide⟩),
   opAt 2853 .MSTORE,
   opAt 2854 (.Swap ⟨0, by decide⟩),
   opAt 2855 (.Swap ⟨1, by decide⟩),
   opAt 2856 .OR,
   opAt 2857 (.Swap ⟨0, by decide⟩),
   pushAt 2858 1 31,
   opAt 2859 .NOT,
   opAt 2860 .ADD,
   pushAt 2861 2 8255,
   opAt 2862 (.Dup ⟨1, by decide⟩),
   opAt 2863 .GT,
   pushAt 2864 2 3734,
   opAt 2865 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2866 .POP,
   pushAt 2867 2 8224,
   opAt 2868 .MLOAD,
   opAt 2869 (.Dup ⟨1, by decide⟩),
   opAt 2870 .ADD,
   opAt 2871 (.Dup ⟨0, by decide⟩),
   pushAt 2872 2 8224,
   opAt 2873 .MSTORE,
   opAt 2874 .LT,
   opAt 2875 .ISZERO,
   pushAt 2876 2 3728,
   opAt 2877 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2878 .JUMPDEST,
   pushAt 2879 2 8224,
   opAt 2880 .MLOAD,
   opAt 2881 .ISZERO,
   pushAt 2882 2 3863,
   opAt 2883 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2884 0 0,
   pushAt 2885 2 9440,
   opAt 2886 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2887 .JUMPDEST,
   opAt 2888 (.Dup ⟨0, by decide⟩),
   opAt 2889 .MLOAD,
   pushAt 2890 2 8256,
   opAt 2891 (.Dup ⟨2, by decide⟩),
   opAt 2892 .SUB,
   opAt 2893 .MLOAD,
   opAt 2894 (.Dup ⟨1, by decide⟩),
   opAt 2895 (.Dup ⟨1, by decide⟩),
   opAt 2896 .GT,
   opAt 2897 (.Swap ⟨1, by decide⟩),
   opAt 2898 .SUB,
   opAt 2899 (.Dup ⟨3, by decide⟩),
   opAt 2900 (.Dup ⟨1, by decide⟩),
   opAt 2901 .LT,
   opAt 2902 (.Swap ⟨0, by decide⟩),
   opAt 2903 (.Dup ⟨4, by decide⟩),
   opAt 2904 (.Swap ⟨0, by decide⟩),
   opAt 2905 .SUB,
   opAt 2906 (.Dup ⟨3, by decide⟩),
   opAt 2907 .MSTORE,
   opAt 2908 .OR,
   opAt 2909 (.Swap ⟨1, by decide⟩),
   opAt 2910 .POP,
   pushAt 2911 1 31,
   opAt 2912 .NOT,
   opAt 2913 .ADD,
   pushAt 2914 2 8255,
   opAt 2915 (.Dup ⟨1, by decide⟩),
   opAt 2916 .GT,
   pushAt 2917 2 3810,
   opAt 2918 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2919 .POP,
   pushAt 2920 2 8224,
   opAt 2921 .MLOAD,
   opAt 2922 .SUB,
   pushAt 2923 2 8224,
   opAt 2924 .MSTORE,
   pushAt 2925 2 3795,
   opAt 2926 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2927 .JUMPDEST,
   pushAt 2928 2 3874,
   pushAt 2929 2 2048,
   pushAt 2930 2 4653,
   opAt 2931 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2932 .JUMPDEST,
   pushAt 2933 1 1,
   opAt 2934 (.Swap ⟨0, by decide⟩),
   opAt 2935 .SUB,
   pushAt 2936 2 3496,
   opAt 2937 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2938 .JUMPDEST,
   opAt 2939 .POP,
   pushAt 2940 2 9344,
   opAt 2941 .MLOAD,
   pushAt 2942 2 5120,
   pushAt 2943 2 4096,
   opAt 2944 .MCOPY,
   pushAt 2945 2 3130,
   opAt 2946 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3290 = true :=
  Artifact.isValidJumpDest_index 2523 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3334 = true :=
  Artifact.isValidJumpDest_index 2550 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3351 = true :=
  Artifact.isValidJumpDest_index 2558 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3358 = true :=
  Artifact.isValidJumpDest_index 2562 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3389 = true :=
  Artifact.isValidJumpDest_index 2586 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3496 = true :=
  Artifact.isValidJumpDest_index 2674 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3612 = true :=
  Artifact.isValidJumpDest_index 2753 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3728 = true :=
  Artifact.isValidJumpDest_index 2826 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3734 = true :=
  Artifact.isValidJumpDest_index 2830 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3795 = true :=
  Artifact.isValidJumpDest_index 2878 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3810 = true :=
  Artifact.isValidJumpDest_index 2887 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3863 = true :=
  Artifact.isValidJumpDest_index 2927 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3874 = true :=
  Artifact.isValidJumpDest_index 2932 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3883 = true :=
  Artifact.isValidJumpDest_index 2938 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
