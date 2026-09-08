import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2500..2511, pc 3585..4657. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2532 .JUMPDEST,
   opAt 2533 (.Dup ⟨0, by decide⟩),
   opAt 2534 (.Dup ⟨3, by decide⟩),
   opAt 2535 .EQ,
   pushAt 2536 0 0,
   opAt 2537 .MLOAD,
   pushAt 2538 1 255,
   opAt 2539 .SHR,
   opAt 2540 .AND,
   opAt 2541 .ISZERO,
   pushAt 2542 2 3604,
   opAt 2543 .JUMPI]

/-- Instructions 2874..2526, pc 3600..3628. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2544 (.Dup ⟨0, by decide⟩),
   pushAt 2545 1 96,
   pushAt 2546 2 1024,
   opAt 2547 .CALLDATACOPY,
   opAt 2548 (.Dup ⟨0, by decide⟩),
   pushAt 2549 1 96,
   pushAt 2550 2 8256,
   opAt 2551 .CALLDATACOPY,
   pushAt 2552 0 0,
   pushAt 2553 2 8224,
   opAt 2554 .MSTORE,
   pushAt 2555 2 3609,
   pushAt 2556 2 2048,
   pushAt 2557 2 2304,
   opAt 2558 .JUMP]

/-- Instructions 2889..2891, pc 4134..3633. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2559 .JUMPDEST,
   pushAt 2560 2 1533,
   opAt 2561 .JUMP]

/-- Instructions 2530..2533, pc 3634..4145. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2562 .JUMPDEST,
   pushAt 2563 1 1,
   pushAt 2564 2 9408,
   opAt 2565 .MLOAD]

/-- Instructions 2534..2914, pc 4146..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2566 .JUMPDEST,
   opAt 2567 (.Dup ⟨0, by decide⟩),
   opAt 2568 .MLOAD,
   opAt 2569 .NOT,
   opAt 2570 (.Dup ⟨2, by decide⟩),
   opAt 2571 .ADD,
   opAt 2572 (.Dup ⟨2, by decide⟩),
   opAt 2573 (.Dup ⟨1, by decide⟩),
   opAt 2574 .LT,
   opAt 2575 (.Swap ⟨2, by decide⟩),
   opAt 2576 .POP,
   opAt 2577 (.Dup ⟨1, by decide⟩),
   pushAt 2578 2 5120,
   opAt 2579 .ADD,
   opAt 2580 .MSTORE,
   opAt 2581 (.Dup ⟨0, by decide⟩),
   opAt 2582 .ISZERO,
   pushAt 2583 2 3647,
   opAt 2584 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3671. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2585 1 31, opAt 2586 .NOT,
   opAt 2587 .ADD,
   pushAt 2588 2 3616,
   opAt 2589 .JUMP]

/-- Instructions 2557..2593, pc 3672..3717. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2590 .JUMPDEST,
   opAt 2591 .POP,
   opAt 2592 .POP,
   pushAt 2593 0 0,
   opAt 2594 .MLOAD,
   opAt 2595 (.Dup ⟨0, by decide⟩),
   pushAt 2596 0 0,
   opAt 2597 .SUB,
   opAt 2598 (.Dup ⟨1, by decide⟩),
   opAt 2599 .AND,
   opAt 2600 (.Dup ⟨0, by decide⟩),
   pushAt 2601 2 6144,
   opAt 2602 .MSTORE,
   opAt 2603 (.Dup ⟨0, by decide⟩),
   opAt 2604 (.Dup ⟨2, by decide⟩),
   opAt 2605 .DIV,
   opAt 2606 (.Dup ⟨0, by decide⟩),
   pushAt 2607 2 6176,
   opAt 2608 .MSTORE,
   opAt 2609 (.Dup ⟨1, by decide⟩),
   pushAt 2610 0 0,
   opAt 2611 .SUB,
   opAt 2612 (.Dup ⟨2, by decide⟩),
   opAt 2613 (.Swap ⟨0, by decide⟩),
   opAt 2614 .DIV,
   pushAt 2615 1 1,
   opAt 2616 .ADD,
   pushAt 2617 2 6208,
   opAt 2618 .MSTORE,
   opAt 2619 (.Dup ⟨0, by decide⟩),
   pushAt 2620 0 0,
   opAt 2621 .SUB,
   opAt 2622 (.Dup ⟨1, by decide⟩),
   opAt 2623 (.Swap ⟨0, by decide⟩),
   opAt 2624 .MOD,
   pushAt 2625 2 6240,
   opAt 2626 .MSTORE]

/-- Instructions 2594..2981, pc 3718..3748. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2627 .JUMPDEST,
   pushAt 2628 1 1,
   opAt 2629 (.Dup ⟨0, by decide⟩),
   opAt 2630 (.Dup ⟨2, by decide⟩),
   opAt 2631 .MUL,
   pushAt 2632 1 2,
   opAt 2633 .SUB,
   opAt 2634 .MUL,
   opAt 2635 (.Dup ⟨0, by decide⟩),
   opAt 2636 (.Dup ⟨2, by decide⟩),
   opAt 2637 .MUL,
   pushAt 2638 1 2,
   opAt 2639 .SUB,
   opAt 2640 .MUL,
   opAt 2641 (.Dup ⟨0, by decide⟩),
   opAt 2642 (.Dup ⟨2, by decide⟩),
   opAt 2643 .MUL,
   pushAt 2644 1 2,
   opAt 2645 .SUB,
   opAt 2646 .MUL,
   opAt 2647 (.Dup ⟨0, by decide⟩),
   opAt 2648 (.Dup ⟨2, by decide⟩),
   opAt 2649 .MUL,
   pushAt 2650 1 2,
   opAt 2651 .SUB,
   opAt 2652 .MUL]

/-- Instructions 2620..3012, pc 3749..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2653 .JUMPDEST,
   opAt 2654 (.Dup ⟨0, by decide⟩),
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
   pushAt 2678 2 6272,
   opAt 2679 .MSTORE,
   opAt 2680 .POP,
   opAt 2681 .POP,
   opAt 2682 .POP,
   opAt 2683 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 3786..3792. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2684 .JUMPDEST,
   opAt 2685 (.Dup ⟨0, by decide⟩),
   opAt 2686 .ISZERO,
   pushAt 2687 2 4196,
   opAt 2688 .JUMPI]

/-- Instructions 2656..2663, pc 3793..3806. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2689 (.Dup ⟨1, by decide⟩),
   pushAt 2690 2 2048,
   pushAt 2691 2 8224,
   opAt 2692 .MCOPY,
   pushAt 2693 0 0,
   pushAt 2694 2 9440,
   opAt 2695 .MLOAD,
   opAt 2696 .MSTORE]

/-- Instructions 3026..2706, pc 4895..3864. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2697 .JUMPDEST,
   pushAt 2698 2 2048,
   opAt 2699 .MLOAD,
   pushAt 2700 2 6144,
   opAt 2701 .MLOAD,
   opAt 2702 (.Dup ⟨1, by decide⟩),
   opAt 2703 (.Dup ⟨1, by decide⟩),
   opAt 2704 (.Swap ⟨0, by decide⟩),
   opAt 2705 .DIV,
   opAt 2706 (.Swap ⟨1, by decide⟩),
   opAt 2707 .MOD,
   pushAt 2708 2 6208,
   opAt 2709 .MLOAD,
   opAt 2710 .MUL,
   pushAt 2711 2 2080,
   opAt 2712 .MLOAD,
   pushAt 2713 2 6144,
   opAt 2714 .MLOAD,
   opAt 2715 (.Swap ⟨0, by decide⟩),
   opAt 2716 .DIV,
   opAt 2717 .ADD,
   pushAt 2718 2 6176,
   opAt 2719 .MLOAD,
   opAt 2720 (.Dup ⟨0, by decide⟩),
   pushAt 2721 2 6240,
   opAt 2722 .MLOAD,
   opAt 2723 (.Dup ⟨4, by decide⟩),
   opAt 2724 .MULMOD,
   opAt 2725 (.Dup ⟨2, by decide⟩),

   opAt 2726 .ADDMOD,
   opAt 2727 (.Swap ⟨0, by decide⟩),
   opAt 2728 .SUB,
   pushAt 2729 2 6272,
   opAt 2730 .MLOAD,
   opAt 2731 .MUL,
   opAt 2732 (.Dup ⟨0, by decide⟩),
   pushAt 2733 0 0,
   opAt 2734 .LT,
   opAt 2735 (.Swap ⟨0, by decide⟩),
   opAt 2736 .SUB,
   opAt 2737 (.Swap ⟨0, by decide⟩),
   pushAt 2738 2 6176,
   opAt 2739 .MLOAD,
   opAt 2740 .JUMPDEST,
   opAt 2741 .GT,
   opAt 2742 .ISZERO,
   pushAt 2743 0 0,
   opAt 2744 .SUB,
   opAt 2745 .OR]

/-- Instructions 2707..3076, pc 3865..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2746 .JUMPDEST,
   pushAt 2747 0 0,
   pushAt 2748 2 9440,
   opAt 2749 .MLOAD,
   pushAt 2750 2 9408,
   opAt 2751 .MLOAD,
   pushAt 2752 2 5120,
   opAt 2753 .ADD]

/-- Instructions 2715..2762, pc 4968..4026. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2754 .JUMPDEST,
   opAt 2755 (.Dup ⟨0, by decide⟩),
   opAt 2756 .MLOAD,
   pushAt 2757 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
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
   pushAt 2786 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2787 .ADD,
   opAt 2788 (.Swap ⟨2, by decide⟩),
   opAt 2789 .MSTORE,
   pushAt 2790 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2791 .ADD,
   pushAt 2792 2 8224,
   opAt 2793 (.Dup ⟨2, by decide⟩),
   opAt 2794 .GT,
   pushAt 2795 2 3863,
   opAt 2796 .JUMPI]

/-- Instructions 2763..2790, pc 4027..4060. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2797 .POP,
   opAt 2798 .POP,
   pushAt 2799 2 8224,
   opAt 2800 .MLOAD,
   opAt 2801 (.Dup ⟨1, by decide⟩),
   opAt 2802 .ADD,
   opAt 2803 (.Dup ⟨1, by decide⟩),
   opAt 2804 (.Dup ⟨1, by decide⟩),
   opAt 2805 .LT,
   opAt 2806 (.Swap ⟨1, by decide⟩),
   opAt 2807 .POP,
   opAt 2808 (.Dup ⟨2, by decide⟩),
   opAt 2809 (.Dup ⟨1, by decide⟩),
   opAt 2810 .LT,
   opAt 2811 (.Swap ⟨0, by decide⟩),
   opAt 2812 (.Dup ⟨3, by decide⟩),
   opAt 2813 (.Swap ⟨0, by decide⟩),
   opAt 2814 .SUB,
   opAt 2815 (.Dup ⟨0, by decide⟩),
   pushAt 2816 2 8224,
   opAt 2817 .MSTORE,
   opAt 2818 .POP,
   opAt 2819 .GT,
   opAt 2820 (.Swap ⟨0, by decide⟩),
   opAt 2821 .POP,
   opAt 2822 .ISZERO,
   pushAt 2823 2 4107,
   opAt 2824 .JUMPI]

/-- Instructions 2791..2794, pc 4061..4066. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2825 .JUMPDEST,
   pushAt 2826 0 0,
   pushAt 2827 2 9440,
   opAt 2828 .MLOAD]

/-- Instructions 2795..3191, pc 4067..4916. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2829 .JUMPDEST,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 .MLOAD,
   opAt 2832 (.Dup ⟨1, by decide⟩),
   pushAt 2833 2 8256,
   opAt 2834 (.Swap ⟨0, by decide⟩),
   opAt 2835 .SUB,
   opAt 2836 .MLOAD,
   opAt 2837 (.Dup ⟨1, by decide⟩),
   opAt 2838 .ADD,
   opAt 2839 (.Dup ⟨0, by decide⟩),
   opAt 2840 (.Dup ⟨2, by decide⟩),
   opAt 2841 .GT,
   opAt 2842 (.Swap ⟨1, by decide⟩),
   opAt 2843 .POP,
   opAt 2844 (.Dup ⟨3, by decide⟩),
   opAt 2845 .ADD,
   opAt 2846 (.Dup ⟨0, by decide⟩),
   opAt 2847 (.Dup ⟨4, by decide⟩),
   opAt 2848 .GT,
   opAt 2849 (.Swap ⟨3, by decide⟩),
   opAt 2850 .POP,
   opAt 2851 (.Dup ⟨2, by decide⟩),
   opAt 2852 .MSTORE,
   opAt 2853 (.Swap ⟨0, by decide⟩),
   opAt 2854 (.Swap ⟨1, by decide⟩),
   opAt 2855 .OR,
   opAt 2856 (.Swap ⟨0, by decide⟩),
   pushAt 2857 1 31, opAt 2858 .NOT,
   opAt 2859 .ADD,
   pushAt 2860 2 8255,
   opAt 2861 (.Dup ⟨1, by decide⟩),
   opAt 2862 .GT,
   pushAt 2863 2 4046,
   opAt 2864 .JUMPI]

/-- Instructions 2830..2841, pc 4917..4965. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2865 .POP,
   pushAt 2866 2 8224,
   opAt 2867 .MLOAD,
   opAt 2868 (.Dup ⟨1, by decide⟩),
   opAt 2869 .ADD,
   opAt 2870 (.Dup ⟨0, by decide⟩),
   pushAt 2871 2 8224,
   opAt 2872 .MSTORE,
   opAt 2873 .LT,
   opAt 2874 .ISZERO,
   pushAt 2875 2 4040,
   opAt 2876 .JUMPI]

/-- Instructions 2842..2847, pc 4966..4137. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2877 .JUMPDEST,
   pushAt 2878 2 8224,
   opAt 2879 .MLOAD,
   opAt 2880 .ISZERO,
   pushAt 2881 2 4176,
   opAt 2882 .JUMPI]

/-- Instructions 2848..2850, pc 4138..4142. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2883 0 0,
   pushAt 2884 2 9440,
   opAt 2885 .MLOAD]

/-- Instructions 2851..2866, pc 4143..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2886 .JUMPDEST,
   opAt 2887 (.Dup ⟨0, by decide⟩),
   opAt 2888 .MLOAD,
   opAt 2889 (.Dup ⟨1, by decide⟩),
   pushAt 2890 2 8256,
   opAt 2891 (.Swap ⟨0, by decide⟩),
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
   pushAt 2911 1 31, opAt 2912 .NOT,
   opAt 2913 .ADD,
   pushAt 2914 2 8255,
   opAt 2915 (.Dup ⟨1, by decide⟩),
   opAt 2916 .GT,
   pushAt 2917 2 4122,
   opAt 2918 .JUMPI]

/-- Instructions 2867..2874, pc 4183..4196. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2919 .POP,
   pushAt 2920 2 8224,
   opAt 2921 .MLOAD,
   opAt 2922 .SUB,
   pushAt 2923 2 8224,
   opAt 2924 .MSTORE,
   pushAt 2925 2 4107,
   opAt 2926 .JUMP]

/-- Instructions 2875..2879, pc 4197..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2927 .JUMPDEST,
   pushAt 2928 2 4187,
   pushAt 2929 2 2048,
   pushAt 2930 2 2304,
   opAt 2931 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2932 .JUMPDEST,
   pushAt 2933 1 1,
   opAt 2934 (.Swap ⟨0, by decide⟩),
   opAt 2935 .SUB,
   pushAt 2936 2 3761,
   opAt 2937 .JUMP]

/-- Instructions 2886..3267, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2938 .JUMPDEST,
   opAt 2939 .POP,
   pushAt 2940 2 1756,
   opAt 2941 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3560 = true :=
  Artifact.isValidJumpDest_index 2532 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3604 = true :=
  Artifact.isValidJumpDest_index 2559 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3609 = true :=
  Artifact.isValidJumpDest_index 2562 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3616 = true :=
  Artifact.isValidJumpDest_index 2566 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3647 = true :=
  Artifact.isValidJumpDest_index 2590 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3693 = true :=
  Artifact.isValidJumpDest_index 2627 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3724 = true :=
  Artifact.isValidJumpDest_index 2653 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3761 = true :=
  Artifact.isValidJumpDest_index 2684 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3782 = true :=
  Artifact.isValidJumpDest_index 2697 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3849 = true :=
  Artifact.isValidJumpDest_index 2746 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3863 = true :=
  Artifact.isValidJumpDest_index 2754 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4040 = true :=
  Artifact.isValidJumpDest_index 2825 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4046 = true :=
  Artifact.isValidJumpDest_index 2829 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4107 = true :=
  Artifact.isValidJumpDest_index 2877 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4122 = true :=
  Artifact.isValidJumpDest_index 2886 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4176 = true :=
  Artifact.isValidJumpDest_index 2927 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4187 = true :=
  Artifact.isValidJumpDest_index 2932 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4196 = true :=
  Artifact.isValidJumpDest_index 2938 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
