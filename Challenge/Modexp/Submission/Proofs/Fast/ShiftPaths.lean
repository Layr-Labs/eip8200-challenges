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
   pushAt 2574 2 4671,
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
   pushAt 2698 2 3918,
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
   pushAt 2760 2 6176,
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
   pushAt 2768 2 9440,
   opAt 2769 .MLOAD,
   pushAt 2770 2 9408,
   opAt 2771 .MLOAD,
   pushAt 2772 2 5120,
   opAt 2773 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2774 .JUMPDEST,
   opAt 2775 (.Dup ⟨0, by decide⟩),
   opAt 2776 .MLOAD,
   pushAt 2777 0 0,
   opAt 2778 .NOT,
   opAt 2779 (.Dup ⟨5, by decide⟩),
   opAt 2780 (.Dup ⟨2, by decide⟩),
   opAt 2781 .MUL,
   opAt 2782 (.Swap ⟨1, by decide⟩),
   opAt 2783 (.Dup ⟨6, by decide⟩),
   opAt 2784 .MULMOD,
   opAt 2785 (.Dup ⟨1, by decide⟩),
   opAt 2786 (.Dup ⟨1, by decide⟩),
   opAt 2787 .LT,
   opAt 2788 .SUB,
   opAt 2789 (.Dup ⟨4, by decide⟩),
   opAt 2790 (.Dup ⟨2, by decide⟩),
   opAt 2791 .ADD,
   opAt 2792 (.Dup ⟨0, by decide⟩),
   opAt 2793 (.Swap ⟨5, by decide⟩),
   opAt 2794 .GT,
   opAt 2795 .SUB,
   opAt 2796 .SUB,
   opAt 2797 (.Dup ⟨3, by decide⟩),
   opAt 2798 (.Dup ⟨3, by decide⟩),
   opAt 2799 .MLOAD,
   opAt 2800 .ADD,
   opAt 2801 (.Dup ⟨0, by decide⟩),
   opAt 2802 (.Swap ⟨4, by decide⟩),
   opAt 2803 .GT,
   opAt 2804 .ADD,
   opAt 2805 (.Swap ⟨2, by decide⟩),
   opAt 2806 (.Dup ⟨2, by decide⟩),
   pushAt 2807 1 31,
   opAt 2808 .NOT,
   opAt 2809 .ADD,
   opAt 2810 (.Swap ⟨2, by decide⟩),
   opAt 2811 .MSTORE,
   pushAt 2812 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2813 .ADD,
   pushAt 2814 2 8224,
   opAt 2815 (.Dup ⟨2, by decide⟩),
   opAt 2816 .GT,
   pushAt 2817 2 3647,
   opAt 2818 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2819 .POP,
   opAt 2820 .POP,
   pushAt 2821 2 8224,
   opAt 2822 .MLOAD,
   opAt 2823 (.Dup ⟨1, by decide⟩),
   opAt 2824 .ADD,
   opAt 2825 (.Dup ⟨1, by decide⟩),
   opAt 2826 (.Dup ⟨1, by decide⟩),
   opAt 2827 .LT,
   opAt 2828 (.Swap ⟨1, by decide⟩),
   opAt 2829 .POP,
   opAt 2830 (.Dup ⟨2, by decide⟩),
   opAt 2831 (.Dup ⟨1, by decide⟩),
   opAt 2832 .LT,
   opAt 2833 (.Swap ⟨0, by decide⟩),
   opAt 2834 (.Dup ⟨3, by decide⟩),
   opAt 2835 (.Swap ⟨0, by decide⟩),
   opAt 2836 .SUB,
   opAt 2837 (.Dup ⟨0, by decide⟩),
   pushAt 2838 2 8224,
   opAt 2839 .MSTORE,
   opAt 2840 .POP,
   opAt 2841 .GT,
   opAt 2842 (.Swap ⟨0, by decide⟩),
   opAt 2843 .POP,
   opAt 2844 .ISZERO,
   pushAt 2845 2 3830,
   opAt 2846 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2847 .JUMPDEST,
   pushAt 2848 0 0,
   pushAt 2849 2 9440,
   opAt 2850 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2851 .JUMPDEST,
   opAt 2852 (.Dup ⟨0, by decide⟩),
   opAt 2853 .MLOAD,
   opAt 2854 (.Dup ⟨1, by decide⟩),
   pushAt 2855 2 8256,
   opAt 2856 (.Swap ⟨0, by decide⟩),
   opAt 2857 .SUB,
   opAt 2858 .MLOAD,
   opAt 2859 (.Dup ⟨1, by decide⟩),
   opAt 2860 .ADD,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   opAt 2862 (.Dup ⟨2, by decide⟩),
   opAt 2863 .GT,
   opAt 2864 (.Swap ⟨1, by decide⟩),
   opAt 2865 .POP,
   opAt 2866 (.Dup ⟨3, by decide⟩),
   opAt 2867 .ADD,
   opAt 2868 (.Dup ⟨0, by decide⟩),
   opAt 2869 (.Dup ⟨4, by decide⟩),
   opAt 2870 .GT,
   opAt 2871 (.Swap ⟨3, by decide⟩),
   opAt 2872 .POP,
   opAt 2873 (.Dup ⟨2, by decide⟩),
   opAt 2874 .MSTORE,
   opAt 2875 (.Swap ⟨0, by decide⟩),
   opAt 2876 (.Swap ⟨1, by decide⟩),
   opAt 2877 .OR,
   opAt 2878 (.Swap ⟨0, by decide⟩),
   pushAt 2879 1 31,
   opAt 2880 .NOT,
   opAt 2881 .ADD,
   pushAt 2882 2 8255,
   opAt 2883 (.Dup ⟨1, by decide⟩),
   opAt 2884 .GT,
   pushAt 2885 2 3769,
   opAt 2886 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2887 .POP,
   pushAt 2888 2 8224,
   opAt 2889 .MLOAD,
   opAt 2890 (.Dup ⟨1, by decide⟩),
   opAt 2891 .ADD,
   opAt 2892 (.Dup ⟨0, by decide⟩),
   pushAt 2893 2 8224,
   opAt 2894 .MSTORE,
   opAt 2895 .LT,
   opAt 2896 .ISZERO,
   pushAt 2897 2 3763,
   opAt 2898 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2899 .JUMPDEST,
   pushAt 2900 2 8224,
   opAt 2901 .MLOAD,
   opAt 2902 .ISZERO,
   pushAt 2903 2 3898,
   opAt 2904 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2905 0 0,
   pushAt 2906 2 9440,
   opAt 2907 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2908 .JUMPDEST,
   opAt 2909 (.Dup ⟨0, by decide⟩),
   opAt 2910 .MLOAD,
   pushAt 2911 2 8256,
   opAt 2912 (.Dup ⟨2, by decide⟩),
   opAt 2913 .SUB,
   opAt 2914 .MLOAD,
   opAt 2915 (.Dup ⟨1, by decide⟩),
   opAt 2916 (.Dup ⟨1, by decide⟩),
   opAt 2917 .GT,
   opAt 2918 (.Swap ⟨1, by decide⟩),
   opAt 2919 .SUB,
   opAt 2920 (.Dup ⟨3, by decide⟩),
   opAt 2921 (.Dup ⟨1, by decide⟩),
   opAt 2922 .LT,
   opAt 2923 (.Swap ⟨0, by decide⟩),
   opAt 2924 (.Dup ⟨4, by decide⟩),
   opAt 2925 (.Swap ⟨0, by decide⟩),
   opAt 2926 .SUB,
   opAt 2927 (.Dup ⟨3, by decide⟩),
   opAt 2928 .MSTORE,
   opAt 2929 .OR,
   opAt 2930 (.Swap ⟨1, by decide⟩),
   opAt 2931 .POP,
   pushAt 2932 1 31,
   opAt 2933 .NOT,
   opAt 2934 .ADD,
   pushAt 2935 2 8255,
   opAt 2936 (.Dup ⟨1, by decide⟩),
   opAt 2937 .GT,
   pushAt 2938 2 3845,
   opAt 2939 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2940 .POP,
   pushAt 2941 2 8224,
   opAt 2942 .MLOAD,
   opAt 2943 .SUB,
   pushAt 2944 2 8224,
   opAt 2945 .MSTORE,
   pushAt 2946 2 3830,
   opAt 2947 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2948 .JUMPDEST,
   pushAt 2949 2 3909,
   pushAt 2950 2 2048,
   pushAt 2951 2 4671,
   opAt 2952 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2953 .JUMPDEST,
   pushAt 2954 1 1,
   opAt 2955 (.Swap ⟨0, by decide⟩),
   opAt 2956 .SUB,
   pushAt 2957 2 3531,
   opAt 2958 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2959 .JUMPDEST,
   opAt 2960 .POP,
   pushAt 2961 2 3179,
   opAt 2962 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3647 = true :=
  Artifact.isValidJumpDest_index 2774 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3763 = true :=
  Artifact.isValidJumpDest_index 2847 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3769 = true :=
  Artifact.isValidJumpDest_index 2851 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3830 = true :=
  Artifact.isValidJumpDest_index 2899 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3845 = true :=
  Artifact.isValidJumpDest_index 2908 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3898 = true :=
  Artifact.isValidJumpDest_index 2948 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3909 = true :=
  Artifact.isValidJumpDest_index 2953 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3918 = true :=
  Artifact.isValidJumpDest_index 2959 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
