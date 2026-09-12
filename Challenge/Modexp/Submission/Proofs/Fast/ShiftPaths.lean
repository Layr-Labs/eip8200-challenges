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
  [opAt 2534 .JUMPDEST,
   opAt 2535 (.Dup ⟨0, by decide⟩),
   opAt 2536 (.Dup ⟨3, by decide⟩),
   opAt 2537 .EQ,
   pushAt 2538 0 0,
   opAt 2539 .MLOAD,
   pushAt 2540 1 255,
   opAt 2541 .SHR,
   opAt 2542 .AND,
   opAt 2543 .ISZERO,
   pushAt 2544 2 3358,
   opAt 2545 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2546 (.Dup ⟨0, by decide⟩),
   pushAt 2547 1 96,
   pushAt 2548 2 1024,
   opAt 2549 .CALLDATACOPY,
   opAt 2550 (.Dup ⟨0, by decide⟩),
   pushAt 2551 1 96,
   pushAt 2552 2 8256,
   opAt 2553 .CALLDATACOPY,
   pushAt 2554 0 0,
   pushAt 2555 2 8224,
   opAt 2556 .MSTORE,
   pushAt 2557 2 3363,
   pushAt 2558 2 2048,
   pushAt 2559 2 4626,
   opAt 2560 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2561 .JUMPDEST,
   pushAt 2562 2 1312,
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
   pushAt 2683 2 3865,
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
   pushAt 2753 1 31,
   opAt 2754 .NOT,
   pushAt 2755 2 9440,
   opAt 2756 .MLOAD,
   pushAt 2757 2 9408,
   opAt 2758 .MLOAD,
   pushAt 2759 2 5120,
   opAt 2760 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2761 .JUMPDEST,
   opAt 2762 (.Dup ⟨0, by decide⟩),
   opAt 2763 .MLOAD,
   pushAt 2764 0 0,
   opAt 2765 .NOT,
   opAt 2766 (.Dup ⟨6, by decide⟩),
   opAt 2767 (.Dup ⟨2, by decide⟩),
   opAt 2768 .MUL,
   opAt 2769 (.Swap ⟨1, by decide⟩),
   opAt 2770 (.Dup ⟨7, by decide⟩),
   opAt 2771 .MULMOD,
   opAt 2772 (.Dup ⟨1, by decide⟩),
   opAt 2773 (.Dup ⟨1, by decide⟩),
   opAt 2774 .LT,
   opAt 2775 .SUB,
   opAt 2776 (.Dup ⟨5, by decide⟩),
   opAt 2777 (.Dup ⟨2, by decide⟩),
   opAt 2778 .ADD,
   opAt 2779 (.Dup ⟨0, by decide⟩),
   opAt 2780 (.Swap ⟨6, by decide⟩),
   opAt 2781 .GT,
   opAt 2782 .SUB,
   opAt 2783 .SUB,
   opAt 2784 (.Dup ⟨4, by decide⟩),
   opAt 2785 (.Dup ⟨3, by decide⟩),
   opAt 2786 .MLOAD,
   opAt 2787 .ADD,
   opAt 2788 (.Dup ⟨0, by decide⟩),
   opAt 2789 (.Swap ⟨5, by decide⟩),
   opAt 2790 .GT,
   opAt 2791 .ADD,
   opAt 2792 (.Swap ⟨3, by decide⟩),
   opAt 2793 (.Dup ⟨2, by decide⟩),
   opAt 2794 (.Dup ⟨4, by decide⟩),
   opAt 2795 .ADD,
   opAt 2796 (.Swap ⟨2, by decide⟩),
   opAt 2797 .MSTORE,
   opAt 2798 (.Dup ⟨2, by decide⟩),
   opAt 2799 .ADD,
   pushAt 2800 2 8224,
   opAt 2801 (.Dup ⟨2, by decide⟩),
   opAt 2802 .GT,
   pushAt 2803 2 3627,
   opAt 2804 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2805 .POP,
   opAt 2806 .POP,
   opAt 2807 .POP,
   pushAt 2808 2 8224,
   opAt 2809 .MLOAD,
   opAt 2810 (.Dup ⟨1, by decide⟩),
   opAt 2811 .ADD,
   opAt 2812 (.Dup ⟨1, by decide⟩),
   opAt 2813 (.Dup ⟨1, by decide⟩),
   opAt 2814 .LT,
   opAt 2815 (.Swap ⟨1, by decide⟩),
   opAt 2816 .POP,
   opAt 2817 (.Dup ⟨2, by decide⟩),
   opAt 2818 (.Dup ⟨1, by decide⟩),
   opAt 2819 .LT,
   opAt 2820 (.Swap ⟨0, by decide⟩),
   opAt 2821 (.Dup ⟨3, by decide⟩),
   opAt 2822 (.Swap ⟨0, by decide⟩),
   opAt 2823 .SUB,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   pushAt 2825 2 8224,
   opAt 2826 .MSTORE,
   opAt 2827 .POP,
   opAt 2828 .GT,
   opAt 2829 (.Swap ⟨0, by decide⟩),
   opAt 2830 .POP,
   opAt 2831 .ISZERO,
   pushAt 2832 2 3777,
   opAt 2833 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2834 .JUMPDEST,
   pushAt 2835 0 0,
   pushAt 2836 2 9440,
   opAt 2837 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2838 .JUMPDEST,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 .MLOAD,
   opAt 2841 (.Dup ⟨1, by decide⟩),
   pushAt 2842 2 8256,
   opAt 2843 (.Swap ⟨0, by decide⟩),
   opAt 2844 .SUB,
   opAt 2845 .MLOAD,
   opAt 2846 (.Dup ⟨1, by decide⟩),
   opAt 2847 .ADD,
   opAt 2848 (.Dup ⟨0, by decide⟩),
   opAt 2849 (.Dup ⟨2, by decide⟩),
   opAt 2850 .GT,
   opAt 2851 (.Swap ⟨1, by decide⟩),
   opAt 2852 .POP,
   opAt 2853 (.Dup ⟨3, by decide⟩),
   opAt 2854 .ADD,
   opAt 2855 (.Dup ⟨0, by decide⟩),
   opAt 2856 (.Dup ⟨4, by decide⟩),
   opAt 2857 .GT,
   opAt 2858 (.Swap ⟨3, by decide⟩),
   opAt 2859 .POP,
   opAt 2860 (.Dup ⟨2, by decide⟩),
   opAt 2861 .MSTORE,
   opAt 2862 (.Swap ⟨0, by decide⟩),
   opAt 2863 (.Swap ⟨1, by decide⟩),
   opAt 2864 .OR,
   opAt 2865 (.Swap ⟨0, by decide⟩),
   pushAt 2866 1 31,
   opAt 2867 .NOT,
   opAt 2868 .ADD,
   pushAt 2869 2 8255,
   opAt 2870 (.Dup ⟨1, by decide⟩),
   opAt 2871 .GT,
   pushAt 2872 2 3716,
   opAt 2873 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2874 .POP,
   pushAt 2875 2 8224,
   opAt 2876 .MLOAD,
   opAt 2877 (.Dup ⟨1, by decide⟩),
   opAt 2878 .ADD,
   opAt 2879 (.Dup ⟨0, by decide⟩),
   pushAt 2880 2 8224,
   opAt 2881 .MSTORE,
   opAt 2882 .LT,
   opAt 2883 .ISZERO,
   pushAt 2884 2 3710,
   opAt 2885 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2886 .JUMPDEST,
   pushAt 2887 2 8224,
   opAt 2888 .MLOAD,
   opAt 2889 .ISZERO,
   pushAt 2890 2 3845,
   opAt 2891 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2892 0 0,
   pushAt 2893 2 9440,
   opAt 2894 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2895 .JUMPDEST,
   opAt 2896 (.Dup ⟨0, by decide⟩),
   opAt 2897 .MLOAD,
   pushAt 2898 2 8256,
   opAt 2899 (.Dup ⟨2, by decide⟩),
   opAt 2900 .SUB,
   opAt 2901 .MLOAD,
   opAt 2902 (.Dup ⟨1, by decide⟩),
   opAt 2903 (.Dup ⟨1, by decide⟩),
   opAt 2904 .GT,
   opAt 2905 (.Swap ⟨1, by decide⟩),
   opAt 2906 .SUB,
   opAt 2907 (.Dup ⟨3, by decide⟩),
   opAt 2908 (.Dup ⟨1, by decide⟩),
   opAt 2909 .LT,
   opAt 2910 (.Swap ⟨0, by decide⟩),
   opAt 2911 (.Dup ⟨4, by decide⟩),
   opAt 2912 (.Swap ⟨0, by decide⟩),
   opAt 2913 .SUB,
   opAt 2914 (.Dup ⟨3, by decide⟩),
   opAt 2915 .MSTORE,
   opAt 2916 .OR,
   opAt 2917 (.Swap ⟨1, by decide⟩),
   opAt 2918 .POP,
   pushAt 2919 1 31,
   opAt 2920 .NOT,
   opAt 2921 .ADD,
   pushAt 2922 2 8255,
   opAt 2923 (.Dup ⟨1, by decide⟩),
   opAt 2924 .GT,
   pushAt 2925 2 3792,
   opAt 2926 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2927 .POP,
   pushAt 2928 2 8224,
   opAt 2929 .MLOAD,
   opAt 2930 .SUB,
   pushAt 2931 2 8224,
   opAt 2932 .MSTORE,
   pushAt 2933 2 3777,
   opAt 2934 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2935 .JUMPDEST,
   pushAt 2936 2 3856,
   pushAt 2937 2 2048,
   pushAt 2938 2 4626,
   opAt 2939 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2940 .JUMPDEST,
   pushAt 2941 1 1,
   opAt 2942 (.Swap ⟨0, by decide⟩),
   opAt 2943 .SUB,
   pushAt 2944 2 3508,
   opAt 2945 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2946 .JUMPDEST,
   opAt 2947 .POP,
   pushAt 2948 2 3150,
   opAt 2949 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3314 = true :=
  Artifact.isValidJumpDest_index 2534 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3358 = true :=
  Artifact.isValidJumpDest_index 2561 (by rfl)

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3627 = true :=
  Artifact.isValidJumpDest_index 2761 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3710 = true :=
  Artifact.isValidJumpDest_index 2834 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3716 = true :=
  Artifact.isValidJumpDest_index 2838 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3777 = true :=
  Artifact.isValidJumpDest_index 2886 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3792 = true :=
  Artifact.isValidJumpDest_index 2895 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3845 = true :=
  Artifact.isValidJumpDest_index 2935 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3856 = true :=
  Artifact.isValidJumpDest_index 2940 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3865 = true :=
  Artifact.isValidJumpDest_index 2946 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
