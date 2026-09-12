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
   pushAt 2540 2 3349,
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
   pushAt 2553 2 3354,
   pushAt 2554 2 2048,
   pushAt 2555 2 4613,
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
   pushAt 2581 2 3392,
   opAt 2582 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2583 1 31,
   opAt 2584 .NOT,
   opAt 2585 .ADD,
   pushAt 2586 2 3361,
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
   pushAt 2679 2 3856,
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
   pushAt 2749 1 31,
   opAt 2750 .NOT,
   pushAt 2751 2 9440,
   opAt 2752 .MLOAD,
   pushAt 2753 2 9408,
   opAt 2754 .MLOAD,
   pushAt 2755 2 5120,
   opAt 2756 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2757 .JUMPDEST,
   opAt 2758 (.Dup ⟨0, by decide⟩),
   opAt 2759 .MLOAD,
   pushAt 2760 0 0,
   opAt 2761 .NOT,
   opAt 2762 (.Dup ⟨6, by decide⟩),
   opAt 2763 (.Dup ⟨2, by decide⟩),
   opAt 2764 .MUL,
   opAt 2765 (.Swap ⟨1, by decide⟩),
   opAt 2766 (.Dup ⟨7, by decide⟩),
   opAt 2767 .MULMOD,
   opAt 2768 (.Dup ⟨1, by decide⟩),
   opAt 2769 (.Dup ⟨1, by decide⟩),
   opAt 2770 .LT,
   opAt 2771 .SUB,
   opAt 2772 (.Dup ⟨5, by decide⟩),
   opAt 2773 (.Dup ⟨2, by decide⟩),
   opAt 2774 .ADD,
   opAt 2775 (.Dup ⟨0, by decide⟩),
   opAt 2776 (.Swap ⟨6, by decide⟩),
   opAt 2777 .GT,
   opAt 2778 .SUB,
   opAt 2779 .SUB,
   opAt 2780 (.Dup ⟨4, by decide⟩),
   opAt 2781 (.Dup ⟨3, by decide⟩),
   opAt 2782 .MLOAD,
   opAt 2783 .ADD,
   opAt 2784 (.Dup ⟨0, by decide⟩),
   opAt 2785 (.Swap ⟨5, by decide⟩),
   opAt 2786 .GT,
   opAt 2787 .ADD,
   opAt 2788 (.Swap ⟨3, by decide⟩),
   opAt 2789 (.Dup ⟨2, by decide⟩),
   opAt 2790 (.Dup ⟨4, by decide⟩),
   opAt 2791 .ADD,
   opAt 2792 (.Swap ⟨2, by decide⟩),
   opAt 2793 .MSTORE,
   opAt 2794 (.Dup ⟨2, by decide⟩),
   opAt 2795 .ADD,
   pushAt 2796 2 8224,
   opAt 2797 (.Dup ⟨2, by decide⟩),
   opAt 2798 .GT,
   pushAt 2799 2 3618,
   opAt 2800 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2801 .POP,
   opAt 2802 .POP,
   opAt 2803 .POP,
   pushAt 2804 2 8224,
   opAt 2805 .MLOAD,
   opAt 2806 (.Dup ⟨1, by decide⟩),
   opAt 2807 .ADD,
   opAt 2808 (.Dup ⟨1, by decide⟩),
   opAt 2809 (.Dup ⟨1, by decide⟩),
   opAt 2810 .LT,
   opAt 2811 (.Swap ⟨1, by decide⟩),
   opAt 2812 .POP,
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 (.Dup ⟨1, by decide⟩),
   opAt 2815 .LT,
   opAt 2816 (.Swap ⟨0, by decide⟩),
   opAt 2817 (.Dup ⟨3, by decide⟩),
   opAt 2818 (.Swap ⟨0, by decide⟩),
   opAt 2819 .SUB,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   pushAt 2821 2 8224,
   opAt 2822 .MSTORE,
   opAt 2823 .POP,
   opAt 2824 .GT,
   opAt 2825 (.Swap ⟨0, by decide⟩),
   opAt 2826 .POP,
   opAt 2827 .ISZERO,
   pushAt 2828 2 3768,
   opAt 2829 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2830 .JUMPDEST,
   pushAt 2831 0 0,
   pushAt 2832 2 9440,
   opAt 2833 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2834 .JUMPDEST,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   opAt 2836 .MLOAD,
   opAt 2837 (.Dup ⟨1, by decide⟩),
   pushAt 2838 2 8256,
   opAt 2839 (.Swap ⟨0, by decide⟩),
   opAt 2840 .SUB,
   opAt 2841 .MLOAD,
   opAt 2842 (.Dup ⟨1, by decide⟩),
   opAt 2843 .ADD,
   opAt 2844 (.Dup ⟨0, by decide⟩),
   opAt 2845 (.Dup ⟨2, by decide⟩),
   opAt 2846 .GT,
   opAt 2847 (.Swap ⟨1, by decide⟩),
   opAt 2848 .POP,
   opAt 2849 (.Dup ⟨3, by decide⟩),
   opAt 2850 .ADD,
   opAt 2851 (.Dup ⟨0, by decide⟩),
   opAt 2852 (.Dup ⟨4, by decide⟩),
   opAt 2853 .GT,
   opAt 2854 (.Swap ⟨3, by decide⟩),
   opAt 2855 .POP,
   opAt 2856 (.Dup ⟨2, by decide⟩),
   opAt 2857 .MSTORE,
   opAt 2858 (.Swap ⟨0, by decide⟩),
   opAt 2859 (.Swap ⟨1, by decide⟩),
   opAt 2860 .OR,
   opAt 2861 (.Swap ⟨0, by decide⟩),
   pushAt 2862 1 31,
   opAt 2863 .NOT,
   opAt 2864 .ADD,
   pushAt 2865 2 8255,
   opAt 2866 (.Dup ⟨1, by decide⟩),
   opAt 2867 .GT,
   pushAt 2868 2 3707,
   opAt 2869 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2870 .POP,
   pushAt 2871 2 8224,
   opAt 2872 .MLOAD,
   opAt 2873 (.Dup ⟨1, by decide⟩),
   opAt 2874 .ADD,
   opAt 2875 (.Dup ⟨0, by decide⟩),
   pushAt 2876 2 8224,
   opAt 2877 .MSTORE,
   opAt 2878 .LT,
   opAt 2879 .ISZERO,
   pushAt 2880 2 3701,
   opAt 2881 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2882 .JUMPDEST,
   pushAt 2883 2 8224,
   opAt 2884 .MLOAD,
   opAt 2885 .ISZERO,
   pushAt 2886 2 3836,
   opAt 2887 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2888 0 0,
   pushAt 2889 2 9440,
   opAt 2890 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2891 .JUMPDEST,
   opAt 2892 (.Dup ⟨0, by decide⟩),
   opAt 2893 .MLOAD,
   pushAt 2894 2 8256,
   opAt 2895 (.Dup ⟨2, by decide⟩),
   opAt 2896 .SUB,
   opAt 2897 .MLOAD,
   opAt 2898 (.Dup ⟨1, by decide⟩),
   opAt 2899 (.Dup ⟨1, by decide⟩),
   opAt 2900 .GT,
   opAt 2901 (.Swap ⟨1, by decide⟩),
   opAt 2902 .SUB,
   opAt 2903 (.Dup ⟨3, by decide⟩),
   opAt 2904 (.Dup ⟨1, by decide⟩),
   opAt 2905 .LT,
   opAt 2906 (.Swap ⟨0, by decide⟩),
   opAt 2907 (.Dup ⟨4, by decide⟩),
   opAt 2908 (.Swap ⟨0, by decide⟩),
   opAt 2909 .SUB,
   opAt 2910 (.Dup ⟨3, by decide⟩),
   opAt 2911 .MSTORE,
   opAt 2912 .OR,
   opAt 2913 (.Swap ⟨1, by decide⟩),
   opAt 2914 .POP,
   pushAt 2915 1 31,
   opAt 2916 .NOT,
   opAt 2917 .ADD,
   pushAt 2918 2 8255,
   opAt 2919 (.Dup ⟨1, by decide⟩),
   opAt 2920 .GT,
   pushAt 2921 2 3783,
   opAt 2922 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2923 .POP,
   pushAt 2924 2 8224,
   opAt 2925 .MLOAD,
   opAt 2926 .SUB,
   pushAt 2927 2 8224,
   opAt 2928 .MSTORE,
   pushAt 2929 2 3768,
   opAt 2930 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2931 .JUMPDEST,
   pushAt 2932 2 3847,
   pushAt 2933 2 2048,
   pushAt 2934 2 4613,
   opAt 2935 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2936 .JUMPDEST,
   pushAt 2937 1 1,
   opAt 2938 (.Swap ⟨0, by decide⟩),
   opAt 2939 .SUB,
   pushAt 2940 2 3499,
   opAt 2941 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2942 .JUMPDEST,
   opAt 2943 .POP,
   pushAt 2944 2 3146,
   opAt 2945 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3305 = true :=
  Artifact.isValidJumpDest_index 2530 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3349 = true :=
  Artifact.isValidJumpDest_index 2557 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3354 = true :=
  Artifact.isValidJumpDest_index 2560 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3361 = true :=
  Artifact.isValidJumpDest_index 2564 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3392 = true :=
  Artifact.isValidJumpDest_index 2588 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3499 = true :=
  Artifact.isValidJumpDest_index 2676 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3618 = true :=
  Artifact.isValidJumpDest_index 2757 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3701 = true :=
  Artifact.isValidJumpDest_index 2830 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3707 = true :=
  Artifact.isValidJumpDest_index 2834 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3768 = true :=
  Artifact.isValidJumpDest_index 2882 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3783 = true :=
  Artifact.isValidJumpDest_index 2891 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3836 = true :=
  Artifact.isValidJumpDest_index 2931 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3847 = true :=
  Artifact.isValidJumpDest_index 2936 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3856 = true :=
  Artifact.isValidJumpDest_index 2942 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
