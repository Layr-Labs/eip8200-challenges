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
  [opAt 2516 .JUMPDEST,
   opAt 2517 (.Dup ⟨0, by decide⟩),
   opAt 2518 (.Dup ⟨3, by decide⟩),
   opAt 2519 .EQ,
   pushAt 2520 0 0,
   opAt 2521 .MLOAD,
   pushAt 2522 1 255,
   opAt 2523 .SHR,
   opAt 2524 .AND,
   opAt 2525 .ISZERO,
   pushAt 2526 2 3604,
   opAt 2527 .JUMPI]

/-- Instructions 2874..2526, pc 3600..3628. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2528 (.Dup ⟨0, by decide⟩),
   pushAt 2529 1 96,
   pushAt 2530 2 1024,
   opAt 2531 .CALLDATACOPY,
   opAt 2532 (.Dup ⟨0, by decide⟩),
   pushAt 2533 1 96,
   pushAt 2534 2 8256,
   opAt 2535 .CALLDATACOPY,
   pushAt 2536 0 0,
   pushAt 2537 2 8224,
   opAt 2538 .MSTORE,
   pushAt 2539 2 3609,
   pushAt 2540 2 2048,
   pushAt 2541 2 2304,
   opAt 2542 .JUMP]

/-- Instructions 2889..2891, pc 4134..3633. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2543 .JUMPDEST,
   pushAt 2544 2 1533,
   opAt 2545 .JUMP]

/-- Instructions 2530..2533, pc 3634..4145. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2546 .JUMPDEST,
   pushAt 2547 1 1,
   pushAt 2548 2 9408,
   opAt 2549 .MLOAD]

/-- Instructions 2534..2914, pc 4146..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2550 .JUMPDEST,
   opAt 2551 (.Dup ⟨0, by decide⟩),
   opAt 2552 .MLOAD,
   opAt 2553 .NOT,
   opAt 2554 (.Dup ⟨2, by decide⟩),
   opAt 2555 .ADD,
   opAt 2556 (.Dup ⟨2, by decide⟩),
   opAt 2557 (.Dup ⟨1, by decide⟩),
   opAt 2558 .LT,
   opAt 2559 (.Swap ⟨2, by decide⟩),
   opAt 2560 .POP,
   opAt 2561 (.Dup ⟨1, by decide⟩),
   pushAt 2562 2 5120,
   opAt 2563 .ADD,
   opAt 2564 .MSTORE,
   opAt 2565 (.Dup ⟨0, by decide⟩),
   opAt 2566 .ISZERO,
   pushAt 2567 2 3647,
   opAt 2568 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3671. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2569 1 31, opAt 2570 .NOT,
   opAt 2571 .ADD,
   pushAt 2572 2 3616,
   opAt 2573 .JUMP]

/-- Instructions 2557..2593, pc 3672..3717. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2574 .JUMPDEST,
   opAt 2575 .POP,
   opAt 2576 .POP,
   pushAt 2577 0 0,
   opAt 2578 .MLOAD,
   opAt 2579 (.Dup ⟨0, by decide⟩),
   pushAt 2580 0 0,
   opAt 2581 .SUB,
   opAt 2582 (.Dup ⟨1, by decide⟩),
   opAt 2583 .AND,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   pushAt 2585 2 6144,
   opAt 2586 .MSTORE,
   opAt 2587 (.Dup ⟨0, by decide⟩),
   opAt 2588 (.Dup ⟨2, by decide⟩),
   opAt 2589 .DIV,
   opAt 2590 (.Dup ⟨0, by decide⟩),
   pushAt 2591 2 6176,
   opAt 2592 .MSTORE,
   opAt 2593 (.Dup ⟨1, by decide⟩),
   pushAt 2594 0 0,
   opAt 2595 .SUB,
   opAt 2596 (.Dup ⟨2, by decide⟩),
   opAt 2597 (.Swap ⟨0, by decide⟩),
   opAt 2598 .DIV,
   pushAt 2599 1 1,
   opAt 2600 .ADD,
   pushAt 2601 2 6208,
   opAt 2602 .MSTORE,
   opAt 2603 (.Dup ⟨0, by decide⟩),
   pushAt 2604 0 0,
   opAt 2605 .SUB,
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 (.Swap ⟨0, by decide⟩),
   opAt 2608 .MOD,
   pushAt 2609 2 6240,
   opAt 2610 .MSTORE]

/-- Instructions 2594..2981, pc 3718..3748. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2611 .JUMPDEST,
   pushAt 2612 1 1,
   opAt 2613 (.Dup ⟨0, by decide⟩),
   opAt 2614 (.Dup ⟨2, by decide⟩),
   opAt 2615 .MUL,
   pushAt 2616 1 2,
   opAt 2617 .SUB,
   opAt 2618 .MUL,
   opAt 2619 (.Dup ⟨0, by decide⟩),
   opAt 2620 (.Dup ⟨2, by decide⟩),
   opAt 2621 .MUL,
   pushAt 2622 1 2,
   opAt 2623 .SUB,
   opAt 2624 .MUL,
   opAt 2625 (.Dup ⟨0, by decide⟩),
   opAt 2626 (.Dup ⟨2, by decide⟩),
   opAt 2627 .MUL,
   pushAt 2628 1 2,
   opAt 2629 .SUB,
   opAt 2630 .MUL,
   opAt 2631 (.Dup ⟨0, by decide⟩),
   opAt 2632 (.Dup ⟨2, by decide⟩),
   opAt 2633 .MUL,
   pushAt 2634 1 2,
   opAt 2635 .SUB,
   opAt 2636 .MUL]

/-- Instructions 2620..3012, pc 3749..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2637 .JUMPDEST,
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
   pushAt 2662 2 6272,
   opAt 2663 .MSTORE,
   opAt 2664 .POP,
   opAt 2665 .POP,
   opAt 2666 .POP,
   opAt 2667 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 3786..3792. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2668 .JUMPDEST,
   opAt 2669 (.Dup ⟨0, by decide⟩),
   opAt 2670 .ISZERO,
   pushAt 2671 2 4196,
   opAt 2672 .JUMPI]

/-- Instructions 2656..2663, pc 3793..3806. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2673 (.Dup ⟨1, by decide⟩),
   pushAt 2674 2 2048,
   pushAt 2675 2 8224,
   opAt 2676 .MCOPY,
   pushAt 2677 0 0,
   pushAt 2678 2 9440,
   opAt 2679 .MLOAD,
   opAt 2680 .MSTORE]

/-- Instructions 3026..2706, pc 4895..3864. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2681 .JUMPDEST,
   pushAt 2682 2 2048,
   opAt 2683 .MLOAD,
   pushAt 2684 2 6144,
   opAt 2685 .MLOAD,
   opAt 2686 (.Dup ⟨1, by decide⟩),
   opAt 2687 (.Dup ⟨1, by decide⟩),
   opAt 2688 (.Swap ⟨0, by decide⟩),
   opAt 2689 .DIV,
   opAt 2690 (.Swap ⟨1, by decide⟩),
   opAt 2691 .MOD,
   pushAt 2692 2 6208,
   opAt 2693 .MLOAD,
   opAt 2694 .MUL,
   pushAt 2695 2 2080,
   opAt 2696 .MLOAD,
   pushAt 2697 2 6144,
   opAt 2698 .MLOAD,
   opAt 2699 (.Swap ⟨0, by decide⟩),
   opAt 2700 .DIV,
   opAt 2701 .ADD,
   pushAt 2702 2 6176,
   opAt 2703 .MLOAD,
   opAt 2704 (.Dup ⟨0, by decide⟩),
   pushAt 2705 2 6240,
   opAt 2706 .MLOAD,
   opAt 2707 (.Dup ⟨4, by decide⟩),
   opAt 2708 .MULMOD,
   opAt 2709 (.Dup ⟨2, by decide⟩),

   opAt 2710 .ADDMOD,
   opAt 2711 (.Swap ⟨0, by decide⟩),
   opAt 2712 .SUB,
   pushAt 2713 2 6272,
   opAt 2714 .MLOAD,
   opAt 2715 .MUL,
   opAt 2716 (.Dup ⟨0, by decide⟩),
   pushAt 2717 0 0,
   opAt 2718 .LT,
   opAt 2719 (.Swap ⟨0, by decide⟩),
   opAt 2720 .SUB,
   opAt 2721 (.Swap ⟨0, by decide⟩),
   pushAt 2722 2 6176,
   opAt 2723 .MLOAD,
   opAt 2724 .JUMPDEST,
   opAt 2725 .GT,
   opAt 2726 .ISZERO,
   pushAt 2727 0 0,
   opAt 2728 .SUB,
   opAt 2729 .OR]

/-- Instructions 2707..3076, pc 3865..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2730 .JUMPDEST,
   pushAt 2731 0 0,
   pushAt 2732 2 9440,
   opAt 2733 .MLOAD,
   pushAt 2734 2 9408,
   opAt 2735 .MLOAD,
   pushAt 2736 2 5120,
   opAt 2737 .ADD]

/-- Instructions 2715..2762, pc 4968..4026. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2738 .JUMPDEST,
   opAt 2739 (.Dup ⟨0, by decide⟩),
   opAt 2740 .MLOAD,
   pushAt 2741 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2742 (.Dup ⟨5, by decide⟩),
   opAt 2743 (.Dup ⟨2, by decide⟩),
   opAt 2744 .MUL,
   opAt 2745 (.Swap ⟨1, by decide⟩),
   opAt 2746 (.Dup ⟨6, by decide⟩),
   opAt 2747 .MULMOD,
   opAt 2748 (.Dup ⟨1, by decide⟩),
   opAt 2749 (.Dup ⟨1, by decide⟩),
   opAt 2750 .LT,
   opAt 2751 .SUB,
   opAt 2752 (.Dup ⟨4, by decide⟩),
   opAt 2753 (.Dup ⟨2, by decide⟩),
   opAt 2754 .ADD,
   opAt 2755 (.Dup ⟨0, by decide⟩),
   opAt 2756 (.Swap ⟨5, by decide⟩),
   opAt 2757 .GT,
   opAt 2758 .SUB,
   opAt 2759 .SUB,
   opAt 2760 (.Dup ⟨3, by decide⟩),
   opAt 2761 (.Dup ⟨3, by decide⟩),
   opAt 2762 .MLOAD,
   opAt 2763 .ADD,
   opAt 2764 (.Dup ⟨0, by decide⟩),
   opAt 2765 (.Swap ⟨4, by decide⟩),
   opAt 2766 .GT,
   opAt 2767 .ADD,
   opAt 2768 (.Swap ⟨2, by decide⟩),
   opAt 2769 (.Dup ⟨2, by decide⟩),
   pushAt 2770 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2771 .ADD,
   opAt 2772 (.Swap ⟨2, by decide⟩),
   opAt 2773 .MSTORE,
   pushAt 2774 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2775 .ADD,
   pushAt 2776 2 8224,
   opAt 2777 (.Dup ⟨2, by decide⟩),
   opAt 2778 .GT,
   pushAt 2779 2 3863,
   opAt 2780 .JUMPI]

/-- Instructions 2763..2790, pc 4027..4060. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2781 .POP,
   opAt 2782 .POP,
   pushAt 2783 2 8224,
   opAt 2784 .MLOAD,
   opAt 2785 (.Dup ⟨1, by decide⟩),
   opAt 2786 .ADD,
   opAt 2787 (.Dup ⟨1, by decide⟩),
   opAt 2788 (.Dup ⟨1, by decide⟩),
   opAt 2789 .LT,
   opAt 2790 (.Swap ⟨1, by decide⟩),
   opAt 2791 .POP,
   opAt 2792 (.Dup ⟨2, by decide⟩),
   opAt 2793 (.Dup ⟨1, by decide⟩),
   opAt 2794 .LT,
   opAt 2795 (.Swap ⟨0, by decide⟩),
   opAt 2796 (.Dup ⟨3, by decide⟩),
   opAt 2797 (.Swap ⟨0, by decide⟩),
   opAt 2798 .SUB,
   opAt 2799 (.Dup ⟨0, by decide⟩),
   pushAt 2800 2 8224,
   opAt 2801 .MSTORE,
   opAt 2802 .POP,
   opAt 2803 .GT,
   opAt 2804 (.Swap ⟨0, by decide⟩),
   opAt 2805 .POP,
   opAt 2806 .ISZERO,
   pushAt 2807 2 4107,
   opAt 2808 .JUMPI]

/-- Instructions 2791..2794, pc 4061..4066. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2809 .JUMPDEST,
   pushAt 2810 0 0,
   pushAt 2811 2 9440,
   opAt 2812 .MLOAD]

/-- Instructions 2795..3191, pc 4067..4916. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2813 .JUMPDEST,
   opAt 2814 (.Dup ⟨0, by decide⟩),
   opAt 2815 .MLOAD,
   opAt 2816 (.Dup ⟨1, by decide⟩),
   pushAt 2817 2 8256,
   opAt 2818 (.Swap ⟨0, by decide⟩),
   opAt 2819 .SUB,
   opAt 2820 .MLOAD,
   opAt 2821 (.Dup ⟨1, by decide⟩),
   opAt 2822 .ADD,
   opAt 2823 (.Dup ⟨0, by decide⟩),
   opAt 2824 (.Dup ⟨2, by decide⟩),
   opAt 2825 .GT,
   opAt 2826 (.Swap ⟨1, by decide⟩),
   opAt 2827 .POP,
   opAt 2828 (.Dup ⟨3, by decide⟩),
   opAt 2829 .ADD,
   opAt 2830 (.Dup ⟨0, by decide⟩),
   opAt 2831 (.Dup ⟨4, by decide⟩),
   opAt 2832 .GT,
   opAt 2833 (.Swap ⟨3, by decide⟩),
   opAt 2834 .POP,
   opAt 2835 (.Dup ⟨2, by decide⟩),
   opAt 2836 .MSTORE,
   opAt 2837 (.Swap ⟨0, by decide⟩),
   opAt 2838 (.Swap ⟨1, by decide⟩),
   opAt 2839 .OR,
   opAt 2840 (.Swap ⟨0, by decide⟩),
   pushAt 2841 1 31, opAt 2842 .NOT,
   opAt 2843 .ADD,
   pushAt 2844 2 8255,
   opAt 2845 (.Dup ⟨1, by decide⟩),
   opAt 2846 .GT,
   pushAt 2847 2 4046,
   opAt 2848 .JUMPI]

/-- Instructions 2830..2841, pc 4917..4965. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2849 .POP,
   pushAt 2850 2 8224,
   opAt 2851 .MLOAD,
   opAt 2852 (.Dup ⟨1, by decide⟩),
   opAt 2853 .ADD,
   opAt 2854 (.Dup ⟨0, by decide⟩),
   pushAt 2855 2 8224,
   opAt 2856 .MSTORE,
   opAt 2857 .LT,
   opAt 2858 .ISZERO,
   pushAt 2859 2 4040,
   opAt 2860 .JUMPI]

/-- Instructions 2842..2847, pc 4966..4137. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2861 .JUMPDEST,
   pushAt 2862 2 8224,
   opAt 2863 .MLOAD,
   opAt 2864 .ISZERO,
   pushAt 2865 2 4176,
   opAt 2866 .JUMPI]

/-- Instructions 2848..2850, pc 4138..4142. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2867 0 0,
   pushAt 2868 2 9440,
   opAt 2869 .MLOAD]

/-- Instructions 2851..2866, pc 4143..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2870 .JUMPDEST,
   opAt 2871 (.Dup ⟨0, by decide⟩),
   opAt 2872 .MLOAD,
   opAt 2873 (.Dup ⟨1, by decide⟩),
   pushAt 2874 2 8256,
   opAt 2875 (.Swap ⟨0, by decide⟩),
   opAt 2876 .SUB,
   opAt 2877 .MLOAD,
   opAt 2878 (.Dup ⟨1, by decide⟩),
   opAt 2879 (.Dup ⟨1, by decide⟩),
   opAt 2880 .GT,
   opAt 2881 (.Swap ⟨1, by decide⟩),
   opAt 2882 .SUB,
   opAt 2883 (.Dup ⟨3, by decide⟩),
   opAt 2884 (.Dup ⟨1, by decide⟩),
   opAt 2885 .LT,
   opAt 2886 (.Swap ⟨0, by decide⟩),
   opAt 2887 (.Dup ⟨4, by decide⟩),
   opAt 2888 (.Swap ⟨0, by decide⟩),
   opAt 2889 .SUB,
   opAt 2890 (.Dup ⟨3, by decide⟩),
   opAt 2891 .MSTORE,
   opAt 2892 .OR,
   opAt 2893 (.Swap ⟨1, by decide⟩),
   opAt 2894 .POP,
   pushAt 2895 1 31, opAt 2896 .NOT,
   opAt 2897 .ADD,
   pushAt 2898 2 8255,
   opAt 2899 (.Dup ⟨1, by decide⟩),
   opAt 2900 .GT,
   pushAt 2901 2 4122,
   opAt 2902 .JUMPI]

/-- Instructions 2867..2874, pc 4183..4196. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2903 .POP,
   pushAt 2904 2 8224,
   opAt 2905 .MLOAD,
   opAt 2906 .SUB,
   pushAt 2907 2 8224,
   opAt 2908 .MSTORE,
   pushAt 2909 2 4107,
   opAt 2910 .JUMP]

/-- Instructions 2875..2879, pc 4197..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2911 .JUMPDEST,
   pushAt 2912 2 4187,
   pushAt 2913 2 2048,
   pushAt 2914 2 2304,
   opAt 2915 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2916 .JUMPDEST,
   pushAt 2917 1 1,
   opAt 2918 (.Swap ⟨0, by decide⟩),
   opAt 2919 .SUB,
   pushAt 2920 2 3761,
   opAt 2921 .JUMP]

/-- Instructions 2886..3267, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2922 .JUMPDEST,
   opAt 2923 .POP,
   pushAt 2924 2 1756,
   opAt 2925 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3560 = true :=
  Artifact.isValidJumpDest_index 2516 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3604 = true :=
  Artifact.isValidJumpDest_index 2543 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3609 = true :=
  Artifact.isValidJumpDest_index 2546 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3616 = true :=
  Artifact.isValidJumpDest_index 2550 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3647 = true :=
  Artifact.isValidJumpDest_index 2574 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3693 = true :=
  Artifact.isValidJumpDest_index 2611 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3724 = true :=
  Artifact.isValidJumpDest_index 2637 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3761 = true :=
  Artifact.isValidJumpDest_index 2668 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3782 = true :=
  Artifact.isValidJumpDest_index 2681 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3849 = true :=
  Artifact.isValidJumpDest_index 2730 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3863 = true :=
  Artifact.isValidJumpDest_index 2738 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4040 = true :=
  Artifact.isValidJumpDest_index 2809 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4046 = true :=
  Artifact.isValidJumpDest_index 2813 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4107 = true :=
  Artifact.isValidJumpDest_index 2861 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4122 = true :=
  Artifact.isValidJumpDest_index 2870 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4176 = true :=
  Artifact.isValidJumpDest_index 2911 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4187 = true :=
  Artifact.isValidJumpDest_index 2916 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4196 = true :=
  Artifact.isValidJumpDest_index 2922 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
