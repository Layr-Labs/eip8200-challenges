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
  [opAt 2511 .JUMPDEST,
   opAt 2512 (.Dup ⟨0, by decide⟩),
   opAt 2513 (.Dup ⟨3, by decide⟩),
   opAt 2514 .EQ,
   pushAt 2515 0 0,
   opAt 2516 .MLOAD,
   pushAt 2517 1 255,
   opAt 2518 .SHR,
   opAt 2519 .AND,
   opAt 2520 .ISZERO,
   pushAt 2521 2 3583,
   opAt 2522 .JUMPI]

/-- Instructions 2874..2526, pc 3600..3628. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2523 (.Dup ⟨0, by decide⟩),
   pushAt 2524 1 96,
   pushAt 2525 2 1024,
   opAt 2526 .CALLDATACOPY,
   opAt 2527 (.Dup ⟨0, by decide⟩),
   pushAt 2528 1 96,
   pushAt 2529 2 8256,
   opAt 2530 .CALLDATACOPY,
   pushAt 2531 0 0,
   pushAt 2532 2 8224,
   opAt 2533 .MSTORE,
   pushAt 2534 2 3588,
   pushAt 2535 2 2048,
   pushAt 2536 2 2292,
   opAt 2537 .JUMP]

/-- Instructions 2889..2891, pc 4134..3633. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2538 .JUMPDEST,
   pushAt 2539 2 1527,
   opAt 2540 .JUMP]

/-- Instructions 2530..2533, pc 3634..4145. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2541 .JUMPDEST,
   pushAt 2542 1 1,
   pushAt 2543 2 9408,
   opAt 2544 .MLOAD]

/-- Instructions 2534..2914, pc 4146..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2545 .JUMPDEST,
   opAt 2546 (.Dup ⟨0, by decide⟩),
   opAt 2547 .MLOAD,
   opAt 2548 .NOT,
   opAt 2549 (.Dup ⟨2, by decide⟩),
   opAt 2550 .ADD,
   opAt 2551 (.Dup ⟨2, by decide⟩),
   opAt 2552 (.Dup ⟨1, by decide⟩),
   opAt 2553 .LT,
   opAt 2554 (.Swap ⟨2, by decide⟩),
   opAt 2555 .POP,
   opAt 2556 (.Dup ⟨1, by decide⟩),
   pushAt 2557 2 5120,
   opAt 2558 .ADD,
   opAt 2559 .MSTORE,
   opAt 2560 (.Dup ⟨0, by decide⟩),
   opAt 2561 .ISZERO,
   pushAt 2562 2 3626,
   opAt 2563 .JUMPI]

/-- Instructions 2915..2556, pc 4722..3671. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2564 1 31, opAt 2565 .NOT,
   opAt 2566 .ADD,
   pushAt 2567 2 3595,
   opAt 2568 .JUMP]

/-- Instructions 2557..2593, pc 3672..3717. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2569 .JUMPDEST,
   opAt 2570 .POP,
   opAt 2571 .POP,
   pushAt 2572 0 0,
   opAt 2573 .MLOAD,
   opAt 2574 (.Dup ⟨0, by decide⟩),
   pushAt 2575 0 0,
   opAt 2576 .SUB,
   opAt 2577 (.Dup ⟨1, by decide⟩),
   opAt 2578 .AND,
   opAt 2579 (.Dup ⟨0, by decide⟩),
   pushAt 2580 2 6144,
   opAt 2581 .MSTORE,
   opAt 2582 (.Dup ⟨0, by decide⟩),
   opAt 2583 (.Dup ⟨2, by decide⟩),
   opAt 2584 .DIV,
   opAt 2585 (.Dup ⟨0, by decide⟩),
   pushAt 2586 2 6176,
   opAt 2587 .MSTORE,
   opAt 2588 (.Dup ⟨1, by decide⟩),
   pushAt 2589 0 0,
   opAt 2590 .SUB,
   opAt 2591 (.Dup ⟨2, by decide⟩),
   opAt 2592 (.Swap ⟨0, by decide⟩),
   opAt 2593 .DIV,
   pushAt 2594 1 1,
   opAt 2595 .ADD,
   pushAt 2596 2 6208,
   opAt 2597 .MSTORE,
   opAt 2598 (.Dup ⟨0, by decide⟩),
   pushAt 2599 0 0,
   opAt 2600 .SUB,
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 (.Swap ⟨0, by decide⟩),
   opAt 2603 .MOD,
   pushAt 2604 2 6240,
   opAt 2605 .MSTORE]

/-- Instructions 2594..2981, pc 3718..3748. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 2606 1 1,
   opAt 2607 (.Dup ⟨0, by decide⟩),
   opAt 2608 (.Dup ⟨2, by decide⟩),
   opAt 2609 .MUL,
   pushAt 2610 1 2,
   opAt 2611 .SUB,
   opAt 2612 .MUL,
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
   opAt 2630 .MUL]

/-- Instructions 2620..3012, pc 3749..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   opAt 2631 (.Dup ⟨0, by decide⟩),
   opAt 2632 (.Dup ⟨2, by decide⟩),
   opAt 2633 .MUL,
   pushAt 2634 1 2,
   opAt 2635 .SUB,
   opAt 2636 .MUL,
   opAt 2637 (.Dup ⟨0, by decide⟩),
   opAt 2638 (.Dup ⟨2, by decide⟩),
   opAt 2639 .MUL,
   pushAt 2640 1 2,
   opAt 2641 .SUB,
   opAt 2642 .MUL,
   opAt 2643 (.Dup ⟨0, by decide⟩),
   opAt 2644 (.Dup ⟨2, by decide⟩),
   opAt 2645 .MUL,
   pushAt 2646 1 2,
   opAt 2647 .SUB,
   opAt 2648 .MUL,
   opAt 2649 (.Dup ⟨0, by decide⟩),
   opAt 2650 (.Dup ⟨2, by decide⟩),
   opAt 2651 .MUL,
   pushAt 2652 1 2,
   opAt 2653 .SUB,
   opAt 2654 .MUL,
   pushAt 2655 2 6272,
   opAt 2656 .MSTORE,
   opAt 2657 .POP,
   opAt 2658 .POP,
   opAt 2659 .POP,
   opAt 2660 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 3786..3792. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2661 .JUMPDEST,
   opAt 2662 (.Dup ⟨0, by decide⟩),
   opAt 2663 .ISZERO,
   pushAt 2664 2 4170,
   opAt 2665 .JUMPI]

/-- Instructions 2656..2663, pc 3793..3806. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2666 (.Dup ⟨1, by decide⟩),
   pushAt 2667 2 2048,
   pushAt 2668 2 8224,
   opAt 2669 .MCOPY,
   pushAt 2670 0 0,
   pushAt 2671 2 9440,
   opAt 2672 .MLOAD,
   opAt 2673 .MSTORE]

/-- Instructions 3026..2706, pc 4895..3864. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 2674 2 2048,
   opAt 2675 .MLOAD,
   pushAt 2676 2 6144,
   opAt 2677 .MLOAD,
   opAt 2678 (.Dup ⟨1, by decide⟩),
   opAt 2679 (.Dup ⟨1, by decide⟩),
   opAt 2680 (.Swap ⟨0, by decide⟩),
   opAt 2681 .DIV,
   opAt 2682 (.Swap ⟨1, by decide⟩),
   opAt 2683 .MOD,
   pushAt 2684 2 6208,
   opAt 2685 .MLOAD,
   opAt 2686 .MUL,
   pushAt 2687 2 2080,
   opAt 2688 .MLOAD,
   pushAt 2689 2 6144,
   opAt 2690 .MLOAD,
   opAt 2691 (.Swap ⟨0, by decide⟩),
   opAt 2692 .DIV,
   opAt 2693 .ADD,
   pushAt 2694 2 6176,
   opAt 2695 .MLOAD,
   opAt 2696 (.Dup ⟨0, by decide⟩),
   pushAt 2697 2 6240,
   opAt 2698 .MLOAD,
   opAt 2699 (.Dup ⟨4, by decide⟩),
   opAt 2700 .MULMOD,
   opAt 2701 (.Dup ⟨2, by decide⟩),

   opAt 2702 .ADDMOD,
   opAt 2703 (.Swap ⟨0, by decide⟩),
   opAt 2704 .SUB,
   pushAt 2705 2 6272,
   opAt 2706 .MLOAD,
   opAt 2707 .MUL,
   opAt 2708 (.Dup ⟨0, by decide⟩),
   pushAt 2709 0 0,
   opAt 2710 .LT,
   opAt 2711 (.Swap ⟨0, by decide⟩),
   opAt 2712 .SUB,
   opAt 2713 (.Swap ⟨0, by decide⟩),
   pushAt 2714 2 6176,
   opAt 2715 .MLOAD,
      opAt 2716 .GT,
   opAt 2717 .ISZERO,
   pushAt 2718 0 0,
   opAt 2719 .SUB,
   opAt 2720 .OR]

/-- Instructions 2707..3076, pc 3865..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   pushAt 2721 0 0,
   pushAt 2722 2 9440,
   opAt 2723 .MLOAD,
   pushAt 2724 2 9408,
   opAt 2725 .MLOAD,
   pushAt 2726 2 5120,
   opAt 2727 .ADD]

/-- Instructions 2715..2762, pc 4968..4026. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2728 .JUMPDEST,
   opAt 2729 (.Dup ⟨0, by decide⟩),
   opAt 2730 .MLOAD,
   pushAt 2731 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2732 (.Dup ⟨5, by decide⟩),
   opAt 2733 (.Dup ⟨2, by decide⟩),
   opAt 2734 .MUL,
   opAt 2735 (.Swap ⟨1, by decide⟩),
   opAt 2736 (.Dup ⟨6, by decide⟩),
   opAt 2737 .MULMOD,
   opAt 2738 (.Dup ⟨1, by decide⟩),
   opAt 2739 (.Dup ⟨1, by decide⟩),
   opAt 2740 .LT,
   opAt 2741 .SUB,
   opAt 2742 (.Dup ⟨4, by decide⟩),
   opAt 2743 (.Dup ⟨2, by decide⟩),
   opAt 2744 .ADD,
   opAt 2745 (.Dup ⟨0, by decide⟩),
   opAt 2746 (.Swap ⟨5, by decide⟩),
   opAt 2747 .GT,
   opAt 2748 .SUB,
   opAt 2749 .SUB,
   opAt 2750 (.Dup ⟨3, by decide⟩),
   opAt 2751 (.Dup ⟨3, by decide⟩),
   opAt 2752 .MLOAD,
   opAt 2753 .ADD,
   opAt 2754 (.Dup ⟨0, by decide⟩),
   opAt 2755 (.Swap ⟨4, by decide⟩),
   opAt 2756 .GT,
   opAt 2757 .ADD,
   opAt 2758 (.Swap ⟨2, by decide⟩),
   opAt 2759 (.Dup ⟨2, by decide⟩),
   pushAt 2760 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2761 .ADD,
   opAt 2762 (.Swap ⟨2, by decide⟩),
   opAt 2763 .MSTORE,
   pushAt 2764 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2765 .ADD,
   pushAt 2766 2 8224,
   opAt 2767 (.Dup ⟨2, by decide⟩),
   opAt 2768 .GT,
   pushAt 2769 2 3837,
   opAt 2770 .JUMPI]

/-- Instructions 2763..2790, pc 4027..4060. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2771 .POP,
   opAt 2772 .POP,
   pushAt 2773 2 8224,
   opAt 2774 .MLOAD,
   opAt 2775 (.Dup ⟨1, by decide⟩),
   opAt 2776 .ADD,
   opAt 2777 (.Dup ⟨1, by decide⟩),
   opAt 2778 (.Dup ⟨1, by decide⟩),
   opAt 2779 .LT,
   opAt 2780 (.Swap ⟨1, by decide⟩),
   opAt 2781 .POP,
   opAt 2782 (.Dup ⟨2, by decide⟩),
   opAt 2783 (.Dup ⟨1, by decide⟩),
   opAt 2784 .LT,
   opAt 2785 (.Swap ⟨0, by decide⟩),
   opAt 2786 (.Dup ⟨3, by decide⟩),
   opAt 2787 (.Swap ⟨0, by decide⟩),
   opAt 2788 .SUB,
   opAt 2789 (.Dup ⟨0, by decide⟩),
   pushAt 2790 2 8224,
   opAt 2791 .MSTORE,
   opAt 2792 .POP,
   opAt 2793 .GT,
   opAt 2794 (.Swap ⟨0, by decide⟩),
   opAt 2795 .POP,
   opAt 2796 .ISZERO,
   pushAt 2797 2 4081,
   opAt 2798 .JUMPI]

/-- Instructions 2791..2794, pc 4061..4066. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2799 .JUMPDEST,
   pushAt 2800 0 0,
   pushAt 2801 2 9440,
   opAt 2802 .MLOAD]

/-- Instructions 2795..3191, pc 4067..4916. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2803 .JUMPDEST,
   opAt 2804 (.Dup ⟨0, by decide⟩),
   opAt 2805 .MLOAD,
   opAt 2806 (.Dup ⟨1, by decide⟩),
   pushAt 2807 2 8256,
   opAt 2808 (.Swap ⟨0, by decide⟩),
   opAt 2809 .SUB,
   opAt 2810 .MLOAD,
   opAt 2811 (.Dup ⟨1, by decide⟩),
   opAt 2812 .ADD,
   opAt 2813 (.Dup ⟨0, by decide⟩),
   opAt 2814 (.Dup ⟨2, by decide⟩),
   opAt 2815 .GT,
   opAt 2816 (.Swap ⟨1, by decide⟩),
   opAt 2817 .POP,
   opAt 2818 (.Dup ⟨3, by decide⟩),
   opAt 2819 .ADD,
   opAt 2820 (.Dup ⟨0, by decide⟩),
   opAt 2821 (.Dup ⟨4, by decide⟩),
   opAt 2822 .GT,
   opAt 2823 (.Swap ⟨3, by decide⟩),
   opAt 2824 .POP,
   opAt 2825 (.Dup ⟨2, by decide⟩),
   opAt 2826 .MSTORE,
   opAt 2827 (.Swap ⟨0, by decide⟩),
   opAt 2828 (.Swap ⟨1, by decide⟩),
   opAt 2829 .OR,
   opAt 2830 (.Swap ⟨0, by decide⟩),
   pushAt 2831 1 31, opAt 2832 .NOT,
   opAt 2833 .ADD,
   pushAt 2834 2 8255,
   opAt 2835 (.Dup ⟨1, by decide⟩),
   opAt 2836 .GT,
   pushAt 2837 2 4020,
   opAt 2838 .JUMPI]

/-- Instructions 2830..2841, pc 4917..4965. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2839 .POP,
   pushAt 2840 2 8224,
   opAt 2841 .MLOAD,
   opAt 2842 (.Dup ⟨1, by decide⟩),
   opAt 2843 .ADD,
   opAt 2844 (.Dup ⟨0, by decide⟩),
   pushAt 2845 2 8224,
   opAt 2846 .MSTORE,
   opAt 2847 .LT,
   opAt 2848 .ISZERO,
   pushAt 2849 2 4014,
   opAt 2850 .JUMPI]

/-- Instructions 2842..2847, pc 4966..4137. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2851 .JUMPDEST,
   pushAt 2852 2 8224,
   opAt 2853 .MLOAD,
   opAt 2854 .ISZERO,
   pushAt 2855 2 4150,
   opAt 2856 .JUMPI]

/-- Instructions 2848..2850, pc 4138..4142. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2857 0 0,
   pushAt 2858 2 9440,
   opAt 2859 .MLOAD]

/-- Instructions 2851..2866, pc 4143..5232. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2860 .JUMPDEST,
   opAt 2861 (.Dup ⟨0, by decide⟩),
   opAt 2862 .MLOAD,
   opAt 2863 (.Dup ⟨1, by decide⟩),
   pushAt 2864 2 8256,
   opAt 2865 (.Swap ⟨0, by decide⟩),
   opAt 2866 .SUB,
   opAt 2867 .MLOAD,
   opAt 2868 (.Dup ⟨1, by decide⟩),
   opAt 2869 (.Dup ⟨1, by decide⟩),
   opAt 2870 .GT,
   opAt 2871 (.Swap ⟨1, by decide⟩),
   opAt 2872 .SUB,
   opAt 2873 (.Dup ⟨3, by decide⟩),
   opAt 2874 (.Dup ⟨1, by decide⟩),
   opAt 2875 .LT,
   opAt 2876 (.Swap ⟨0, by decide⟩),
   opAt 2877 (.Dup ⟨4, by decide⟩),
   opAt 2878 (.Swap ⟨0, by decide⟩),
   opAt 2879 .SUB,
   opAt 2880 (.Dup ⟨3, by decide⟩),
   opAt 2881 .MSTORE,
   opAt 2882 .OR,
   opAt 2883 (.Swap ⟨1, by decide⟩),
   opAt 2884 .POP,
   pushAt 2885 1 31, opAt 2886 .NOT,
   opAt 2887 .ADD,
   pushAt 2888 2 8255,
   opAt 2889 (.Dup ⟨1, by decide⟩),
   opAt 2890 .GT,
   pushAt 2891 2 4096,
   opAt 2892 .JUMPI]

/-- Instructions 2867..2874, pc 4183..4196. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2893 .POP,
   pushAt 2894 2 8224,
   opAt 2895 .MLOAD,
   opAt 2896 .SUB,
   pushAt 2897 2 8224,
   opAt 2898 .MSTORE,
   pushAt 2899 2 4081,
   opAt 2900 .JUMP]

/-- Instructions 2875..2879, pc 4197..5257. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2901 .JUMPDEST,
   pushAt 2902 2 4161,
   pushAt 2903 2 2048,
   pushAt 2904 2 2292,
   opAt 2905 .JUMP]

/-- Instructions 2880..2885, pc 5357..5296. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2906 .JUMPDEST,
   pushAt 2907 1 1,
   opAt 2908 (.Swap ⟨0, by decide⟩),
   opAt 2909 .SUB,
   pushAt 2910 2 3738,
   opAt 2911 .JUMP]

/-- Instructions 2886..3267, pc 5297..5332. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2912 .JUMPDEST,
   opAt 2913 .POP,
   pushAt 2914 2 1748,
   opAt 2915 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3539 = true :=
  Artifact.isValidJumpDest_index 2511 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3583 = true :=
  Artifact.isValidJumpDest_index 2538 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3588 = true :=
  Artifact.isValidJumpDest_index 2541 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3595 = true :=
  Artifact.isValidJumpDest_index 2545 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3626 = true :=
  Artifact.isValidJumpDest_index 2569 (by rfl)



theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3738 = true :=
  Artifact.isValidJumpDest_index 2661 (by rfl)



theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3837 = true :=
  Artifact.isValidJumpDest_index 2728 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4014 = true :=
  Artifact.isValidJumpDest_index 2799 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4020 = true :=
  Artifact.isValidJumpDest_index 2803 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4081 = true :=
  Artifact.isValidJumpDest_index 2851 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4096 = true :=
  Artifact.isValidJumpDest_index 2860 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4150 = true :=
  Artifact.isValidJumpDest_index 2901 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4161 = true :=
  Artifact.isValidJumpDest_index 2906 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4170 = true :=
  Artifact.isValidJumpDest_index 2912 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
