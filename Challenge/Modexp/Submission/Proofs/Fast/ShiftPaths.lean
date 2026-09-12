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
   pushAt 2539 2 3346,
   opAt 2540 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2541 (.Dup ⟨0, by decide⟩),
   pushAt 2542 1 96,
   pushAt 2543 2 1024,
   opAt 2544 .CALLDATACOPY,
   opAt 2545 (.Dup ⟨0, by decide⟩),
   pushAt 2546 1 96,
   pushAt 2547 2 8256,
   opAt 2548 .CALLDATACOPY,
   pushAt 2549 0 0,
   pushAt 2550 2 8224,
   opAt 2551 .MSTORE,
   pushAt 2552 2 3363,
   pushAt 2553 2 2048,
   pushAt 2554 2 4669,
   opAt 2555 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2556 .JUMPDEST,
   pushAt 2557 1 1,
   pushAt 2558 2 4096,
   opAt 2559 .MSTORE,
   pushAt 2560 2 1300,
   pushAt 2561 2 4096,
   pushAt 2562 2 2081,
   opAt 2563 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2564 .JUMPDEST,
   pushAt 2565 1 1,
   pushAt 2566 2 9408,
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
   pushAt 2580 2 5120,
   opAt 2581 .ADD,
   opAt 2582 .MSTORE,
   opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 .ISZERO,
   pushAt 2585 2 3401,
   opAt 2586 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2587 1 31,
   opAt 2588 .NOT,
   opAt 2589 .ADD,
   pushAt 2590 2 3370,
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
   pushAt 2603 2 6144,
   opAt 2604 .MSTORE,
   opAt 2605 (.Dup ⟨0, by decide⟩),
   opAt 2606 (.Dup ⟨2, by decide⟩),
   opAt 2607 .DIV,
   opAt 2608 (.Dup ⟨0, by decide⟩),
   pushAt 2609 2 6176,
   opAt 2610 .MSTORE,
   opAt 2611 (.Dup ⟨1, by decide⟩),
   pushAt 2612 0 0,
   opAt 2613 .SUB,
   opAt 2614 (.Dup ⟨2, by decide⟩),
   opAt 2615 (.Swap ⟨0, by decide⟩),
   opAt 2616 .DIV,
   pushAt 2617 1 1,
   opAt 2618 .ADD,
   pushAt 2619 2 6208,
   opAt 2620 .MSTORE,
   opAt 2621 (.Dup ⟨0, by decide⟩),
   pushAt 2622 0 0,
   opAt 2623 .SUB,
   opAt 2624 (.Dup ⟨1, by decide⟩),
   opAt 2625 (.Swap ⟨0, by decide⟩),
   opAt 2626 .MOD,
   pushAt 2627 2 6240,
   opAt 2628 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2629 (.Dup ⟨0, by decide⟩),
   pushAt 2630 1 2,
   opAt 2631 .SUB,
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
   opAt 2643 .MUL,
   opAt 2644 (.Dup ⟨0, by decide⟩),
   opAt 2645 (.Dup ⟨2, by decide⟩),
   opAt 2646 .MUL,
   pushAt 2647 1 2,
   opAt 2648 .SUB,
   opAt 2649 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2650 (.Dup ⟨0, by decide⟩),
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
   opAt 2668 (.Dup ⟨0, by decide⟩),
   opAt 2669 (.Dup ⟨2, by decide⟩),
   opAt 2670 .MUL,
   pushAt 2671 1 2,
   opAt 2672 .SUB,
   opAt 2673 .MUL,
   pushAt 2674 2 6272,
   opAt 2675 .MSTORE,
   opAt 2676 .POP,
   opAt 2677 .POP,
   opAt 2678 .POP,
   opAt 2679 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2680 .JUMPDEST,
   opAt 2681 (.Dup ⟨0, by decide⟩),
   opAt 2682 .ISZERO,
   pushAt 2683 2 3895,
   opAt 2684 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2685 (.Dup ⟨1, by decide⟩),
   pushAt 2686 2 2048,
   pushAt 2687 2 8224,
   opAt 2688 .MCOPY,
   pushAt 2689 0 0,
   pushAt 2690 2 9440,
   opAt 2691 .MLOAD,
   opAt 2692 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2693 2 2048,
   opAt 2694 .MLOAD,
   pushAt 2695 2 6144,
   opAt 2696 .MLOAD,
   opAt 2697 (.Dup ⟨0, by decide⟩),
   opAt 2698 (.Dup ⟨2, by decide⟩),
   opAt 2699 .DIV,
   opAt 2700 (.Swap ⟨1, by decide⟩),
   opAt 2701 .MOD,
   pushAt 2702 2 6208,
   opAt 2703 .MLOAD,
   opAt 2704 .MUL,
   pushAt 2705 2 2080,
   opAt 2706 .MLOAD,
   pushAt 2707 2 6144,
   opAt 2708 .MLOAD,
   opAt 2709 (.Swap ⟨0, by decide⟩),
   opAt 2710 .DIV,
   opAt 2711 .ADD,
   pushAt 2712 2 6176,
   opAt 2713 .MLOAD,
   opAt 2714 (.Dup ⟨0, by decide⟩),
   pushAt 2715 2 6240,
   opAt 2716 .MLOAD,
   opAt 2717 (.Dup ⟨4, by decide⟩),
   opAt 2718 .MULMOD,
   opAt 2719 (.Dup ⟨2, by decide⟩),
   opAt 2720 .ADDMOD,
   opAt 2721 (.Swap ⟨0, by decide⟩),
   opAt 2722 .SUB,
   pushAt 2723 2 6272,
   opAt 2724 .MLOAD,
   opAt 2725 .MUL,
   opAt 2726 (.Dup ⟨0, by decide⟩),
   pushAt 2727 0 0,
   opAt 2728 .MLOAD,
   opAt 2729 .MUL,
   pushAt 2730 2 2080,
   opAt 2731 .MLOAD,
   opAt 2732 .SUB,
   pushAt 2733 1 32,
   opAt 2734 .MLOAD,
   pushAt 2735 1 128,
   opAt 2736 .SHR,
   opAt 2737 (.Dup ⟨2, by decide⟩),
   pushAt 2738 1 128,
   opAt 2739 .SHR,
   opAt 2740 .MUL,
   opAt 2741 .GT,
   opAt 2742 (.Swap ⟨0, by decide⟩),
   opAt 2743 .SUB,
   opAt 2744 (.Swap ⟨0, by decide⟩),
   pushAt 2745 2 6176,
   opAt 2746 .MLOAD,
   opAt 2747 .GT,
   opAt 2748 .ISZERO,
   pushAt 2749 0 0,
   opAt 2750 .SUB,
   opAt 2751 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2752 0 0,
   pushAt 2753 2 9440,
   opAt 2754 .MLOAD,
   pushAt 2755 2 9408,
   opAt 2756 .MLOAD,
   pushAt 2757 2 5120,
   opAt 2758 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2759 .JUMPDEST,
   opAt 2760 (.Dup ⟨0, by decide⟩),
   opAt 2761 .MLOAD,
   pushAt 2762 0 0,
   opAt 2763 .NOT,
   opAt 2764 (.Dup ⟨5, by decide⟩),
   opAt 2765 (.Dup ⟨2, by decide⟩),
   opAt 2766 .MUL,
   opAt 2767 (.Swap ⟨1, by decide⟩),
   opAt 2768 (.Dup ⟨6, by decide⟩),
   opAt 2769 .MULMOD,
   opAt 2770 (.Dup ⟨1, by decide⟩),
   opAt 2771 (.Dup ⟨1, by decide⟩),
   opAt 2772 .LT,
   opAt 2773 .SUB,
   opAt 2774 (.Dup ⟨4, by decide⟩),
   opAt 2775 (.Dup ⟨2, by decide⟩),
   opAt 2776 .ADD,
   opAt 2777 (.Dup ⟨0, by decide⟩),
   opAt 2778 (.Swap ⟨5, by decide⟩),
   opAt 2779 .GT,
   opAt 2780 .SUB,
   opAt 2781 .SUB,
   opAt 2782 (.Dup ⟨3, by decide⟩),
   opAt 2783 (.Dup ⟨3, by decide⟩),
   opAt 2784 .MLOAD,
   opAt 2785 .ADD,
   opAt 2786 (.Dup ⟨0, by decide⟩),
   opAt 2787 (.Swap ⟨4, by decide⟩),
   opAt 2788 .GT,
   opAt 2789 .ADD,
   opAt 2790 (.Swap ⟨2, by decide⟩),
   opAt 2791 (.Dup ⟨2, by decide⟩),
   pushAt 2792 1 31,
   opAt 2793 .NOT,
   opAt 2794 .ADD,
   opAt 2795 (.Swap ⟨2, by decide⟩),
   opAt 2796 .MSTORE,
   pushAt 2797 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2798 .ADD,
   pushAt 2799 2 8224,
   opAt 2800 (.Dup ⟨2, by decide⟩),
   opAt 2801 .GT,
   pushAt 2802 2 3624,
   opAt 2803 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2804 .POP,
   opAt 2805 .POP,
   pushAt 2806 2 8224,
   opAt 2807 .MLOAD,
   opAt 2808 (.Dup ⟨1, by decide⟩),
   opAt 2809 .ADD,
   opAt 2810 (.Dup ⟨1, by decide⟩),
   opAt 2811 (.Dup ⟨1, by decide⟩),
   opAt 2812 .LT,
   opAt 2813 (.Swap ⟨1, by decide⟩),
   opAt 2814 .POP,
   opAt 2815 (.Dup ⟨2, by decide⟩),
   opAt 2816 (.Dup ⟨1, by decide⟩),
   opAt 2817 .LT,
   opAt 2818 (.Swap ⟨0, by decide⟩),
   opAt 2819 (.Dup ⟨3, by decide⟩),
   opAt 2820 (.Swap ⟨0, by decide⟩),
   opAt 2821 .SUB,
   opAt 2822 (.Dup ⟨0, by decide⟩),
   pushAt 2823 2 8224,
   opAt 2824 .MSTORE,
   opAt 2825 .POP,
   opAt 2826 .GT,
   opAt 2827 (.Swap ⟨0, by decide⟩),
   opAt 2828 .POP,
   opAt 2829 .ISZERO,
   pushAt 2830 2 3807,
   opAt 2831 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2832 .JUMPDEST,
   pushAt 2833 0 0,
   pushAt 2834 2 9440,
   opAt 2835 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2836 .JUMPDEST,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   opAt 2838 .MLOAD,
   opAt 2839 (.Dup ⟨1, by decide⟩),
   pushAt 2840 2 8256,
   opAt 2841 (.Swap ⟨0, by decide⟩),
   opAt 2842 .SUB,
   opAt 2843 .MLOAD,
   opAt 2844 (.Dup ⟨1, by decide⟩),
   opAt 2845 .ADD,
   opAt 2846 (.Dup ⟨0, by decide⟩),
   opAt 2847 (.Dup ⟨2, by decide⟩),
   opAt 2848 .GT,
   opAt 2849 (.Swap ⟨1, by decide⟩),
   opAt 2850 .POP,
   opAt 2851 (.Dup ⟨3, by decide⟩),
   opAt 2852 .ADD,
   opAt 2853 (.Dup ⟨0, by decide⟩),
   opAt 2854 (.Dup ⟨4, by decide⟩),
   opAt 2855 .GT,
   opAt 2856 (.Swap ⟨3, by decide⟩),
   opAt 2857 .POP,
   opAt 2858 (.Dup ⟨2, by decide⟩),
   opAt 2859 .MSTORE,
   opAt 2860 (.Swap ⟨0, by decide⟩),
   opAt 2861 (.Swap ⟨1, by decide⟩),
   opAt 2862 .OR,
   opAt 2863 (.Swap ⟨0, by decide⟩),
   pushAt 2864 1 31,
   opAt 2865 .NOT,
   opAt 2866 .ADD,
   pushAt 2867 2 8255,
   opAt 2868 (.Dup ⟨1, by decide⟩),
   opAt 2869 .GT,
   pushAt 2870 2 3746,
   opAt 2871 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2872 .POP,
   pushAt 2873 2 8224,
   opAt 2874 .MLOAD,
   opAt 2875 (.Dup ⟨1, by decide⟩),
   opAt 2876 .ADD,
   opAt 2877 (.Dup ⟨0, by decide⟩),
   pushAt 2878 2 8224,
   opAt 2879 .MSTORE,
   opAt 2880 .LT,
   opAt 2881 .ISZERO,
   pushAt 2882 2 3740,
   opAt 2883 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2884 .JUMPDEST,
   pushAt 2885 2 8224,
   opAt 2886 .MLOAD,
   opAt 2887 .ISZERO,
   pushAt 2888 2 3875,
   opAt 2889 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2890 0 0,
   pushAt 2891 2 9440,
   opAt 2892 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2893 .JUMPDEST,
   opAt 2894 (.Dup ⟨0, by decide⟩),
   opAt 2895 .MLOAD,
   pushAt 2896 2 8256,
   opAt 2897 (.Dup ⟨2, by decide⟩),
   opAt 2898 .SUB,
   opAt 2899 .MLOAD,
   opAt 2900 (.Dup ⟨1, by decide⟩),
   opAt 2901 (.Dup ⟨1, by decide⟩),
   opAt 2902 .GT,
   opAt 2903 (.Swap ⟨1, by decide⟩),
   opAt 2904 .SUB,
   opAt 2905 (.Dup ⟨3, by decide⟩),
   opAt 2906 (.Dup ⟨1, by decide⟩),
   opAt 2907 .LT,
   opAt 2908 (.Swap ⟨0, by decide⟩),
   opAt 2909 (.Dup ⟨4, by decide⟩),
   opAt 2910 (.Swap ⟨0, by decide⟩),
   opAt 2911 .SUB,
   opAt 2912 (.Dup ⟨3, by decide⟩),
   opAt 2913 .MSTORE,
   opAt 2914 .OR,
   opAt 2915 (.Swap ⟨1, by decide⟩),
   opAt 2916 .POP,
   pushAt 2917 1 31,
   opAt 2918 .NOT,
   opAt 2919 .ADD,
   pushAt 2920 2 8255,
   opAt 2921 (.Dup ⟨1, by decide⟩),
   opAt 2922 .GT,
   pushAt 2923 2 3822,
   opAt 2924 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2925 .POP,
   pushAt 2926 2 8224,
   opAt 2927 .MLOAD,
   opAt 2928 .SUB,
   pushAt 2929 2 8224,
   opAt 2930 .MSTORE,
   pushAt 2931 2 3807,
   opAt 2932 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2933 .JUMPDEST,
   pushAt 2934 2 3886,
   pushAt 2935 2 2048,
   pushAt 2936 2 4669,
   opAt 2937 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2938 .JUMPDEST,
   pushAt 2939 0 0,
   opAt 2940 .NOT,
   opAt 2941 .ADD,
   pushAt 2942 3 3508,
   opAt 2943 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2944 .JUMPDEST,
   opAt 2945 .POP,
   pushAt 2946 2 9344,
   opAt 2947 .MLOAD,
   pushAt 2948 2 5120,
   pushAt 2949 2 4096,
   opAt 2950 .MCOPY,
   pushAt 2951 2 3138,
   opAt 2952 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3302 = true :=
  Artifact.isValidJumpDest_index 2529 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3346 = true :=
  Artifact.isValidJumpDest_index 2556 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3363 = true :=
  Artifact.isValidJumpDest_index 2564 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3370 = true :=
  Artifact.isValidJumpDest_index 2568 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3401 = true :=
  Artifact.isValidJumpDest_index 2592 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3508 = true :=
  Artifact.isValidJumpDest_index 2680 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3624 = true :=
  Artifact.isValidJumpDest_index 2759 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3740 = true :=
  Artifact.isValidJumpDest_index 2832 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3746 = true :=
  Artifact.isValidJumpDest_index 2836 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3807 = true :=
  Artifact.isValidJumpDest_index 2884 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3822 = true :=
  Artifact.isValidJumpDest_index 2893 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3875 = true :=
  Artifact.isValidJumpDest_index 2933 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3886 = true :=
  Artifact.isValidJumpDest_index 2938 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3895 = true :=
  Artifact.isValidJumpDest_index 2944 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
