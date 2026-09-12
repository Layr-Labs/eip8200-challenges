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
  [opAt 2549 .JUMPDEST,
   opAt 2550 (.Dup ⟨0, by decide⟩),
   opAt 2551 (.Dup ⟨3, by decide⟩),
   opAt 2552 .EQ,
   pushAt 2553 0 0,
   opAt 2554 .MLOAD,
   pushAt 2555 1 255,
   opAt 2556 .SHR,
   opAt 2557 .AND,
   opAt 2558 .ISZERO,
   pushAt 2559 2 3381,
   opAt 2560 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2561 (.Dup ⟨0, by decide⟩),
   pushAt 2562 1 96,
   pushAt 2563 2 1024,
   opAt 2564 .CALLDATACOPY,
   opAt 2565 (.Dup ⟨0, by decide⟩),
   pushAt 2566 1 96,
   pushAt 2567 2 8256,
   opAt 2568 .CALLDATACOPY,
   pushAt 2569 0 0,
   pushAt 2570 2 8224,
   opAt 2571 .MSTORE,
   pushAt 2572 2 3386,
   pushAt 2573 2 2048,
   pushAt 2574 2 4667,
   opAt 2575 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2576 .JUMPDEST,
   pushAt 2577 2 1333,
   opAt 2578 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .JUMPDEST,
   pushAt 2580 1 1,
   pushAt 2581 2 9408,
   opAt 2582 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .JUMPDEST,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   opAt 2585 .MLOAD,
   opAt 2586 .NOT,
   opAt 2587 (.Dup ⟨2, by decide⟩),
   opAt 2588 .ADD,
   opAt 2589 (.Dup ⟨2, by decide⟩),
   opAt 2590 (.Dup ⟨1, by decide⟩),
   opAt 2591 .LT,
   opAt 2592 (.Swap ⟨2, by decide⟩),
   opAt 2593 .POP,
   opAt 2594 (.Dup ⟨1, by decide⟩),
   pushAt 2595 2 5120,
   opAt 2596 .ADD,
   opAt 2597 .MSTORE,
   opAt 2598 (.Dup ⟨0, by decide⟩),
   opAt 2599 .ISZERO,
   pushAt 2600 2 3424,
   opAt 2601 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2602 1 31,
   opAt 2603 .NOT,
   opAt 2604 .ADD,
   pushAt 2605 2 3393,
   opAt 2606 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2607 .JUMPDEST,
   opAt 2608 .POP,
   opAt 2609 .POP,
   pushAt 2610 0 0,
   opAt 2611 .MLOAD,
   opAt 2612 (.Dup ⟨0, by decide⟩),
   pushAt 2613 0 0,
   opAt 2614 .SUB,
   opAt 2615 (.Dup ⟨1, by decide⟩),
   opAt 2616 .AND,
   opAt 2617 (.Dup ⟨0, by decide⟩),
   pushAt 2618 2 6144,
   opAt 2619 .MSTORE,
   opAt 2620 (.Dup ⟨0, by decide⟩),
   opAt 2621 (.Dup ⟨2, by decide⟩),
   opAt 2622 .DIV,
   opAt 2623 (.Dup ⟨0, by decide⟩),
   pushAt 2624 2 6176,
   opAt 2625 .MSTORE,
   opAt 2626 (.Dup ⟨1, by decide⟩),
   pushAt 2627 0 0,
   opAt 2628 .SUB,
   opAt 2629 (.Dup ⟨2, by decide⟩),
   opAt 2630 (.Swap ⟨0, by decide⟩),
   opAt 2631 .DIV,
   pushAt 2632 1 1,
   opAt 2633 .ADD,
   pushAt 2634 2 6208,
   opAt 2635 .MSTORE,
   opAt 2636 (.Dup ⟨0, by decide⟩),
   pushAt 2637 0 0,
   opAt 2638 .SUB,
   opAt 2639 (.Dup ⟨1, by decide⟩),
   opAt 2640 (.Swap ⟨0, by decide⟩),
   opAt 2641 .MOD,
   pushAt 2642 2 6240,
   opAt 2643 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2644 (.Dup ⟨0, by decide⟩),
   pushAt 2645 1 2,
   opAt 2646 .SUB,
   opAt 2647 (.Dup ⟨0, by decide⟩),
   opAt 2648 (.Dup ⟨2, by decide⟩),
   opAt 2649 .MUL,
   pushAt 2650 1 2,
   opAt 2651 .SUB,
   opAt 2652 .MUL,
   opAt 2653 (.Dup ⟨0, by decide⟩),
   opAt 2654 (.Dup ⟨2, by decide⟩),
   opAt 2655 .MUL,
   pushAt 2656 1 2,
   opAt 2657 .SUB,
   opAt 2658 .MUL,
   opAt 2659 (.Dup ⟨0, by decide⟩),
   opAt 2660 (.Dup ⟨2, by decide⟩),
   opAt 2661 .MUL,
   pushAt 2662 1 2,
   opAt 2663 .SUB,
   opAt 2664 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2665 (.Dup ⟨0, by decide⟩),
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
   opAt 2676 .MUL,
   opAt 2677 (.Dup ⟨0, by decide⟩),
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
   pushAt 2689 2 6272,
   opAt 2690 .MSTORE,
   opAt 2691 .POP,
   opAt 2692 .POP,
   opAt 2693 .POP,
   opAt 2694 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2695 .JUMPDEST,
   opAt 2696 (.Dup ⟨0, by decide⟩),
   opAt 2697 .ISZERO,
   pushAt 2698 2 3914,
   opAt 2699 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2700 (.Dup ⟨1, by decide⟩),
   pushAt 2701 2 2048,
   pushAt 2702 2 8224,
   opAt 2703 .MCOPY,
   pushAt 2704 0 0,
   pushAt 2705 2 9440,
   opAt 2706 .MLOAD,
   opAt 2707 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2708 2 2048,
   opAt 2709 .MLOAD,
   pushAt 2710 2 6144,
   opAt 2711 .MLOAD,
   opAt 2712 (.Dup ⟨0, by decide⟩),
   opAt 2713 (.Dup ⟨2, by decide⟩),
   opAt 2714 .DIV,
   opAt 2715 (.Swap ⟨1, by decide⟩),
   opAt 2716 .MOD,
   pushAt 2717 2 6208,
   opAt 2718 .MLOAD,
   opAt 2719 .MUL,
   pushAt 2720 2 2080,
   opAt 2721 .MLOAD,
   pushAt 2722 2 6144,
   opAt 2723 .MLOAD,
   opAt 2724 (.Swap ⟨0, by decide⟩),
   opAt 2725 .DIV,
   opAt 2726 .ADD,
   pushAt 2727 2 6176,
   opAt 2728 .MLOAD,
   opAt 2729 (.Dup ⟨0, by decide⟩),
   pushAt 2730 2 6240,
   opAt 2731 .MLOAD,
   opAt 2732 (.Dup ⟨4, by decide⟩),
   opAt 2733 .MULMOD,
   opAt 2734 (.Dup ⟨2, by decide⟩),
   opAt 2735 .ADDMOD,
   opAt 2736 (.Swap ⟨0, by decide⟩),
   opAt 2737 .SUB,
   pushAt 2738 2 6272,
   opAt 2739 .MLOAD,
   opAt 2740 .MUL,
   opAt 2741 (.Dup ⟨0, by decide⟩),
   pushAt 2742 0 0,
   opAt 2743 .MLOAD,
   opAt 2744 .MUL,
   pushAt 2745 2 2080,
   opAt 2746 .MLOAD,
   opAt 2747 .SUB,
   pushAt 2748 1 32,
   opAt 2749 .MLOAD,
   opAt 2750 .GT,
   opAt 2751 (.Dup ⟨1, by decide⟩),
   pushAt 2752 0 0,
   opAt 2753 .LT,
   opAt 2754 .AND,
   opAt 2755 (.Swap ⟨0, by decide⟩),
   opAt 2756 .SUB,
   opAt 2757 (.Swap ⟨0, by decide⟩),
   pushAt 2758 2 6176,
   opAt 2759 .MLOAD,
   opAt 2760 .GT,
   opAt 2761 .ISZERO,
   pushAt 2762 0 0,
   opAt 2763 .SUB,
   opAt 2764 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2765 0 0,
   pushAt 2766 2 9440,
   opAt 2767 .MLOAD,
   pushAt 2768 2 9408,
   opAt 2769 .MLOAD,
   pushAt 2770 2 5120,
   opAt 2771 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2772 .JUMPDEST,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   opAt 2774 .MLOAD,
   pushAt 2775 0 0,
   opAt 2776 .NOT,
   opAt 2777 (.Dup ⟨5, by decide⟩),
   opAt 2778 (.Dup ⟨2, by decide⟩),
   opAt 2779 .MUL,
   opAt 2780 (.Swap ⟨1, by decide⟩),
   opAt 2781 (.Dup ⟨6, by decide⟩),
   opAt 2782 .MULMOD,
   opAt 2783 (.Dup ⟨1, by decide⟩),
   opAt 2784 (.Dup ⟨1, by decide⟩),
   opAt 2785 .LT,
   opAt 2786 .SUB,
   opAt 2787 (.Dup ⟨4, by decide⟩),
   opAt 2788 (.Dup ⟨2, by decide⟩),
   opAt 2789 .ADD,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   opAt 2791 (.Swap ⟨5, by decide⟩),
   opAt 2792 .GT,
   opAt 2793 .SUB,
   opAt 2794 .SUB,
   opAt 2795 (.Dup ⟨3, by decide⟩),
   opAt 2796 (.Dup ⟨3, by decide⟩),
   opAt 2797 .MLOAD,
   opAt 2798 .ADD,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   opAt 2800 (.Swap ⟨4, by decide⟩),
   opAt 2801 .GT,
   opAt 2802 .ADD,
   opAt 2803 (.Swap ⟨2, by decide⟩),
   opAt 2804 (.Dup ⟨2, by decide⟩),
   pushAt 2805 1 31,
   opAt 2806 .NOT,
   opAt 2807 .ADD,
   opAt 2808 (.Swap ⟨2, by decide⟩),
   opAt 2809 .MSTORE,
   pushAt 2810 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2811 .ADD,
   pushAt 2812 2 8224,
   opAt 2813 (.Dup ⟨2, by decide⟩),
   opAt 2814 .GT,
   pushAt 2815 2 3643,
   opAt 2816 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2817 .POP,
   opAt 2818 .POP,
   pushAt 2819 2 8224,
   opAt 2820 .MLOAD,
   opAt 2821 (.Dup ⟨1, by decide⟩),
   opAt 2822 .ADD,
   opAt 2823 (.Dup ⟨1, by decide⟩),
   opAt 2824 (.Dup ⟨1, by decide⟩),
   opAt 2825 .LT,
   opAt 2826 (.Swap ⟨1, by decide⟩),
   opAt 2827 .POP,
   opAt 2828 (.Dup ⟨2, by decide⟩),
   opAt 2829 (.Dup ⟨1, by decide⟩),
   opAt 2830 .LT,
   opAt 2831 (.Swap ⟨0, by decide⟩),
   opAt 2832 (.Dup ⟨3, by decide⟩),
   opAt 2833 (.Swap ⟨0, by decide⟩),
   opAt 2834 .SUB,
   opAt 2835 (.Dup ⟨0, by decide⟩),
   pushAt 2836 2 8224,
   opAt 2837 .MSTORE,
   opAt 2838 .POP,
   opAt 2839 .GT,
   opAt 2840 (.Swap ⟨0, by decide⟩),
   opAt 2841 .POP,
   opAt 2842 .ISZERO,
   pushAt 2843 2 3826,
   opAt 2844 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2845 .JUMPDEST,
   pushAt 2846 0 0,
   pushAt 2847 2 9440,
   opAt 2848 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2849 .JUMPDEST,
   opAt 2850 (.Dup ⟨0, by decide⟩),
   opAt 2851 .MLOAD,
   opAt 2852 (.Dup ⟨1, by decide⟩),
   pushAt 2853 2 8256,
   opAt 2854 (.Swap ⟨0, by decide⟩),
   opAt 2855 .SUB,
   opAt 2856 .MLOAD,
   opAt 2857 (.Dup ⟨1, by decide⟩),
   opAt 2858 .ADD,
   opAt 2859 (.Dup ⟨0, by decide⟩),
   opAt 2860 (.Dup ⟨2, by decide⟩),
   opAt 2861 .GT,
   opAt 2862 (.Swap ⟨1, by decide⟩),
   opAt 2863 .POP,
   opAt 2864 (.Dup ⟨3, by decide⟩),
   opAt 2865 .ADD,
   opAt 2866 (.Dup ⟨0, by decide⟩),
   opAt 2867 (.Dup ⟨4, by decide⟩),
   opAt 2868 .GT,
   opAt 2869 (.Swap ⟨3, by decide⟩),
   opAt 2870 .POP,
   opAt 2871 (.Dup ⟨2, by decide⟩),
   opAt 2872 .MSTORE,
   opAt 2873 (.Swap ⟨0, by decide⟩),
   opAt 2874 (.Swap ⟨1, by decide⟩),
   opAt 2875 .OR,
   opAt 2876 (.Swap ⟨0, by decide⟩),
   pushAt 2877 1 31,
   opAt 2878 .NOT,
   opAt 2879 .ADD,
   pushAt 2880 2 8255,
   opAt 2881 (.Dup ⟨1, by decide⟩),
   opAt 2882 .GT,
   pushAt 2883 2 3765,
   opAt 2884 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2885 .POP,
   pushAt 2886 2 8224,
   opAt 2887 .MLOAD,
   opAt 2888 (.Dup ⟨1, by decide⟩),
   opAt 2889 .ADD,
   opAt 2890 (.Dup ⟨0, by decide⟩),
   pushAt 2891 2 8224,
   opAt 2892 .MSTORE,
   opAt 2893 .LT,
   opAt 2894 .ISZERO,
   pushAt 2895 2 3759,
   opAt 2896 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2897 .JUMPDEST,
   pushAt 2898 2 8224,
   opAt 2899 .MLOAD,
   opAt 2900 .ISZERO,
   pushAt 2901 2 3894,
   opAt 2902 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2903 0 0,
   pushAt 2904 2 9440,
   opAt 2905 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2906 .JUMPDEST,
   opAt 2907 (.Dup ⟨0, by decide⟩),
   opAt 2908 .MLOAD,
   pushAt 2909 2 8256,
   opAt 2910 (.Dup ⟨2, by decide⟩),
   opAt 2911 .SUB,
   opAt 2912 .MLOAD,
   opAt 2913 (.Dup ⟨1, by decide⟩),
   opAt 2914 (.Dup ⟨1, by decide⟩),
   opAt 2915 .GT,
   opAt 2916 (.Swap ⟨1, by decide⟩),
   opAt 2917 .SUB,
   opAt 2918 (.Dup ⟨3, by decide⟩),
   opAt 2919 (.Dup ⟨1, by decide⟩),
   opAt 2920 .LT,
   opAt 2921 (.Swap ⟨0, by decide⟩),
   opAt 2922 (.Dup ⟨4, by decide⟩),
   opAt 2923 (.Swap ⟨0, by decide⟩),
   opAt 2924 .SUB,
   opAt 2925 (.Dup ⟨3, by decide⟩),
   opAt 2926 .MSTORE,
   opAt 2927 .OR,
   opAt 2928 (.Swap ⟨1, by decide⟩),
   opAt 2929 .POP,
   pushAt 2930 1 31,
   opAt 2931 .NOT,
   opAt 2932 .ADD,
   pushAt 2933 2 8255,
   opAt 2934 (.Dup ⟨1, by decide⟩),
   opAt 2935 .GT,
   pushAt 2936 2 3841,
   opAt 2937 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2938 .POP,
   pushAt 2939 2 8224,
   opAt 2940 .MLOAD,
   opAt 2941 .SUB,
   pushAt 2942 2 8224,
   opAt 2943 .MSTORE,
   pushAt 2944 2 3826,
   opAt 2945 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2946 .JUMPDEST,
   pushAt 2947 2 3905,
   pushAt 2948 2 2048,
   pushAt 2949 2 4667,
   opAt 2950 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2951 .JUMPDEST,
   pushAt 2952 1 1,
   opAt 2953 (.Swap ⟨0, by decide⟩),
   opAt 2954 .SUB,
   pushAt 2955 2 3531,
   opAt 2956 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2957 .JUMPDEST,
   opAt 2958 .POP,
   pushAt 2959 2 3179,
   opAt 2960 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3337 = true :=
  Artifact.isValidJumpDest_index 2549 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3381 = true :=
  Artifact.isValidJumpDest_index 2576 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3386 = true :=
  Artifact.isValidJumpDest_index 2579 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3393 = true :=
  Artifact.isValidJumpDest_index 2583 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3424 = true :=
  Artifact.isValidJumpDest_index 2607 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3531 = true :=
  Artifact.isValidJumpDest_index 2695 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3643 = true :=
  Artifact.isValidJumpDest_index 2772 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3759 = true :=
  Artifact.isValidJumpDest_index 2845 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3765 = true :=
  Artifact.isValidJumpDest_index 2849 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3826 = true :=
  Artifact.isValidJumpDest_index 2897 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3841 = true :=
  Artifact.isValidJumpDest_index 2906 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3894 = true :=
  Artifact.isValidJumpDest_index 2946 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3905 = true :=
  Artifact.isValidJumpDest_index 2951 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3914 = true :=
  Artifact.isValidJumpDest_index 2957 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
