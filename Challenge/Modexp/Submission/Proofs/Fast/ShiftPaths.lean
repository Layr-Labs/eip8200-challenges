import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 2862..2873, pc 4077..4657. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2504 .JUMPDEST,
   opAt 2505 (.Dup ⟨0, by decide⟩),
   opAt 2506 (.Dup ⟨3, by decide⟩),
   opAt 2507 .EQ,
   pushAt 2508 0 0,
   opAt 2509 .MLOAD,
   pushAt 2510 1 255,
   opAt 2511 .SHR,
   opAt 2512 .AND,
   opAt 2513 .ISZERO,
   pushAt 2514 2 4096,
   opAt 2515 .JUMPI]

/-- Instructions 2874..2888, pc 4092..4120. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2516 (.Dup ⟨0, by decide⟩),
   pushAt 2517 1 96,
   pushAt 2518 2 1024,
   opAt 2519 .CALLDATACOPY,
   opAt 2520 (.Dup ⟨0, by decide⟩),
   pushAt 2521 1 96,
   pushAt 2522 2 8256,
   opAt 2523 .CALLDATACOPY,
   pushAt 2524 0 0,
   pushAt 2525 2 8224,
   opAt 2526 .MSTORE,
   pushAt 2527 2 4101,
   pushAt 2528 2 2048,
   pushAt 2529 2 2637,
   opAt 2530 .JUMP]

/-- Instructions 2889..2891, pc 4687..4125. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2531 .JUMPDEST,
   pushAt 2532 2 1533,
   opAt 2533 .JUMP]

/-- Instructions 2892..2895, pc 4126..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2534 .JUMPDEST,
   pushAt 2535 1 1,
   pushAt 2536 2 9408,
   opAt 2537 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2538 .JUMPDEST,
   opAt 2539 (.Dup ⟨0, by decide⟩),
   opAt 2540 .MLOAD,
   opAt 2541 .NOT,
   opAt 2542 (.Dup ⟨2, by decide⟩),
   opAt 2543 .ADD,
   opAt 2544 (.Dup ⟨2, by decide⟩),
   opAt 2545 (.Dup ⟨1, by decide⟩),
   opAt 2546 .LT,
   opAt 2547 (.Swap ⟨2, by decide⟩),
   opAt 2548 .POP,
   opAt 2549 (.Dup ⟨1, by decide⟩),
   pushAt 2550 2 5120,
   opAt 2551 .ADD,
   opAt 2552 .MSTORE,
   opAt 2553 (.Dup ⟨0, by decide⟩),
   opAt 2554 .ISZERO,
   pushAt 2555 2 4169,
   opAt 2556 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4193. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2557 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2558 .ADD,
   pushAt 2559 2 4108,
   opAt 2560 .JUMP]

/-- Instructions 2919..2955, pc 4194..4239. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2561 .JUMPDEST,
   opAt 2562 .POP,
   opAt 2563 .POP,
   pushAt 2564 0 0,
   opAt 2565 .MLOAD,
   opAt 2566 (.Dup ⟨0, by decide⟩),
   pushAt 2567 0 0,
   opAt 2568 .SUB,
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .AND,
   opAt 2571 (.Dup ⟨0, by decide⟩),
   pushAt 2572 2 6144,
   opAt 2573 .MSTORE,
   opAt 2574 (.Dup ⟨0, by decide⟩),
   opAt 2575 (.Dup ⟨2, by decide⟩),
   opAt 2576 .DIV,
   opAt 2577 (.Dup ⟨0, by decide⟩),
   pushAt 2578 2 6176,
   opAt 2579 .MSTORE,
   opAt 2580 (.Dup ⟨1, by decide⟩),
   pushAt 2581 0 0,
   opAt 2582 .SUB,
   opAt 2583 (.Dup ⟨2, by decide⟩),
   opAt 2584 (.Swap ⟨0, by decide⟩),
   opAt 2585 .DIV,
   pushAt 2586 1 1,
   opAt 2587 .ADD,
   pushAt 2588 2 6208,
   opAt 2589 .MSTORE,
   opAt 2590 (.Dup ⟨0, by decide⟩),
   pushAt 2591 0 0,
   opAt 2592 .SUB,
   opAt 2593 (.Dup ⟨1, by decide⟩),
   opAt 2594 (.Swap ⟨0, by decide⟩),
   opAt 2595 .MOD,
   pushAt 2596 2 6240,
   opAt 2597 .MSTORE]

/-- Instructions 2956..2981, pc 4240..4270. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2598 .JUMPDEST,
   pushAt 2599 1 1,
   opAt 2600 (.Dup ⟨0, by decide⟩),
   opAt 2601 (.Dup ⟨2, by decide⟩),
   opAt 2602 .MUL,
   pushAt 2603 1 2,
   opAt 2604 .SUB,
   opAt 2605 .MUL,
   opAt 2606 (.Dup ⟨0, by decide⟩),
   opAt 2607 (.Dup ⟨2, by decide⟩),
   opAt 2608 .MUL,
   pushAt 2609 1 2,
   opAt 2610 .SUB,
   opAt 2611 .MUL,
   opAt 2612 (.Dup ⟨0, by decide⟩),
   opAt 2613 (.Dup ⟨2, by decide⟩),
   opAt 2614 .MUL,
   pushAt 2615 1 2,
   opAt 2616 .SUB,
   opAt 2617 .MUL,
   opAt 2618 (.Dup ⟨0, by decide⟩),
   opAt 2619 (.Dup ⟨2, by decide⟩),
   opAt 2620 .MUL,
   pushAt 2621 1 2,
   opAt 2622 .SUB,
   opAt 2623 .MUL]

/-- Instructions 2982..3012, pc 4271..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2624 .JUMPDEST,
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
   pushAt 2649 2 6272,
   opAt 2650 .MSTORE,
   opAt 2651 .POP,
   opAt 2652 .POP,
   opAt 2653 .POP,
   opAt 2654 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4308..4314. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2655 .JUMPDEST,
   opAt 2656 (.Dup ⟨0, by decide⟩),
   opAt 2657 .ISZERO,
   pushAt 2658 2 4779,
   opAt 2659 .JUMPI]

/-- Instructions 3018..3025, pc 4315..4328. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2660 (.Dup ⟨1, by decide⟩),
   pushAt 2661 2 2048,
   pushAt 2662 2 8224,
   opAt 2663 .MCOPY,
   pushAt 2664 0 0,
   pushAt 2665 2 9440,
   opAt 2666 .MLOAD,
   opAt 2667 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4387. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2668 .JUMPDEST,
   pushAt 2669 2 2048,
   opAt 2670 .MLOAD,
   pushAt 2671 2 6144,
   opAt 2672 .MLOAD,
   opAt 2673 (.Dup ⟨1, by decide⟩),
   opAt 2674 (.Dup ⟨1, by decide⟩),
   opAt 2675 (.Swap ⟨0, by decide⟩),
   opAt 2676 .DIV,
   opAt 2677 (.Swap ⟨1, by decide⟩),
   opAt 2678 .MOD,
   pushAt 2679 2 6208,
   opAt 2680 .MLOAD,
   opAt 2681 .MUL,
   pushAt 2682 2 2080,
   opAt 2683 .MLOAD,
   pushAt 2684 2 6144,
   opAt 2685 .MLOAD,
   opAt 2686 (.Swap ⟨0, by decide⟩),
   opAt 2687 .DIV,
   opAt 2688 .ADD,
   pushAt 2689 2 6176,
   opAt 2690 .MLOAD,
   opAt 2691 (.Dup ⟨0, by decide⟩),
   pushAt 2692 2 6240,
   opAt 2693 .MLOAD,
   opAt 2694 (.Dup ⟨4, by decide⟩),
   opAt 2695 .MULMOD,
   opAt 2696 (.Dup ⟨2, by decide⟩),
   opAt 2697 .JUMPDEST,
   opAt 2698 .ADDMOD,
   opAt 2699 (.Swap ⟨0, by decide⟩),
   opAt 2700 .SUB,
   pushAt 2701 2 6272,
   opAt 2702 .MLOAD,
   opAt 2703 .MUL,
   opAt 2704 (.Dup ⟨0, by decide⟩),
   pushAt 2705 0 0,
   opAt 2706 .LT,
   opAt 2707 (.Swap ⟨0, by decide⟩),
   opAt 2708 .SUB,
   opAt 2709 (.Swap ⟨0, by decide⟩),
   pushAt 2710 2 6176,
   opAt 2711 .MLOAD,
   opAt 2712 .JUMPDEST,
   opAt 2713 .GT,
   opAt 2714 .ISZERO,
   pushAt 2715 0 0,
   opAt 2716 .SUB,
   opAt 2717 .OR]

/-- Instructions 3069..3076, pc 4388..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2718 .JUMPDEST,
   pushAt 2719 0 0,
   pushAt 2720 2 9440,
   opAt 2721 .MLOAD,
   pushAt 2722 2 9408,
   opAt 2723 .MLOAD,
   pushAt 2724 2 5120,
   opAt 2725 .ADD]

/-- Instructions 3077..3124, pc 4968..4549. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2726 .JUMPDEST,
   opAt 2727 (.Dup ⟨0, by decide⟩),
   opAt 2728 .MLOAD,
   pushAt 2729 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2730 (.Dup ⟨5, by decide⟩),
   opAt 2731 (.Dup ⟨2, by decide⟩),
   opAt 2732 .MUL,
   opAt 2733 (.Swap ⟨1, by decide⟩),
   opAt 2734 (.Dup ⟨6, by decide⟩),
   opAt 2735 .MULMOD,
   opAt 2736 (.Dup ⟨1, by decide⟩),
   opAt 2737 (.Dup ⟨1, by decide⟩),
   opAt 2738 .LT,
   opAt 2739 .SUB,
   opAt 2740 (.Dup ⟨4, by decide⟩),
   opAt 2741 (.Dup ⟨2, by decide⟩),
   opAt 2742 .ADD,
   opAt 2743 (.Dup ⟨0, by decide⟩),
   opAt 2744 (.Swap ⟨5, by decide⟩),
   opAt 2745 .GT,
   opAt 2746 .SUB,
   opAt 2747 .SUB,
   opAt 2748 (.Dup ⟨3, by decide⟩),
   opAt 2749 (.Dup ⟨3, by decide⟩),
   opAt 2750 .MLOAD,
   opAt 2751 .ADD,
   opAt 2752 (.Dup ⟨0, by decide⟩),
   opAt 2753 (.Swap ⟨4, by decide⟩),
   opAt 2754 .GT,
   opAt 2755 .ADD,
   opAt 2756 (.Swap ⟨2, by decide⟩),
   opAt 2757 (.Dup ⟨2, by decide⟩),
   pushAt 2758 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2759 .ADD,
   opAt 2760 (.Swap ⟨2, by decide⟩),
   opAt 2761 .MSTORE,
   pushAt 2762 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2763 .ADD,
   pushAt 2764 2 8224,
   opAt 2765 (.Dup ⟨2, by decide⟩),
   opAt 2766 .GT,
   pushAt 2767 2 4386,
   opAt 2768 .JUMPI]

/-- Instructions 3125..3152, pc 4550..4583. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2769 .POP,
   opAt 2770 .POP,
   pushAt 2771 2 8224,
   opAt 2772 .MLOAD,
   opAt 2773 (.Dup ⟨1, by decide⟩),
   opAt 2774 .ADD,
   opAt 2775 (.Dup ⟨1, by decide⟩),
   opAt 2776 (.Dup ⟨1, by decide⟩),
   opAt 2777 .LT,
   opAt 2778 (.Swap ⟨1, by decide⟩),
   opAt 2779 .POP,
   opAt 2780 (.Dup ⟨2, by decide⟩),
   opAt 2781 (.Dup ⟨1, by decide⟩),
   opAt 2782 .LT,
   opAt 2783 (.Swap ⟨0, by decide⟩),
   opAt 2784 (.Dup ⟨3, by decide⟩),
   opAt 2785 (.Swap ⟨0, by decide⟩),
   opAt 2786 .SUB,
   opAt 2787 (.Dup ⟨0, by decide⟩),
   pushAt 2788 2 8224,
   opAt 2789 .MSTORE,
   opAt 2790 .POP,
   opAt 2791 .GT,
   opAt 2792 (.Swap ⟨0, by decide⟩),
   opAt 2793 .POP,
   opAt 2794 .ISZERO,
   pushAt 2795 2 4660,
   opAt 2796 .JUMPI]

/-- Instructions 3153..3156, pc 4584..4589. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2797 .JUMPDEST,
   pushAt 2798 0 0,
   pushAt 2799 2 9440,
   opAt 2800 .MLOAD]

/-- Instructions 3157..3191, pc 4590..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2801 .JUMPDEST,
   opAt 2802 (.Dup ⟨0, by decide⟩),
   opAt 2803 .MLOAD,
   opAt 2804 (.Dup ⟨1, by decide⟩),
   pushAt 2805 2 8256,
   opAt 2806 (.Swap ⟨0, by decide⟩),
   opAt 2807 .SUB,
   opAt 2808 .MLOAD,
   opAt 2809 (.Dup ⟨1, by decide⟩),
   opAt 2810 .ADD,
   opAt 2811 (.Dup ⟨0, by decide⟩),
   opAt 2812 (.Dup ⟨2, by decide⟩),
   opAt 2813 .GT,
   opAt 2814 (.Swap ⟨1, by decide⟩),
   opAt 2815 .POP,
   opAt 2816 (.Dup ⟨3, by decide⟩),
   opAt 2817 .ADD,
   opAt 2818 (.Dup ⟨0, by decide⟩),
   opAt 2819 (.Dup ⟨4, by decide⟩),
   opAt 2820 .GT,
   opAt 2821 (.Swap ⟨3, by decide⟩),
   opAt 2822 .POP,
   opAt 2823 (.Dup ⟨2, by decide⟩),
   opAt 2824 .MSTORE,
   opAt 2825 (.Swap ⟨0, by decide⟩),
   opAt 2826 (.Swap ⟨1, by decide⟩),
   opAt 2827 .OR,
   opAt 2828 (.Swap ⟨0, by decide⟩),
   pushAt 2829 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2830 .ADD,
   pushAt 2831 2 8255,
   opAt 2832 (.Dup ⟨1, by decide⟩),
   opAt 2833 .GT,
   pushAt 2834 2 4569,
   opAt 2835 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2836 .POP,
   pushAt 2837 2 8224,
   opAt 2838 .MLOAD,
   opAt 2839 (.Dup ⟨1, by decide⟩),
   opAt 2840 .ADD,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   pushAt 2842 2 8224,
   opAt 2843 .MSTORE,
   opAt 2844 .LT,
   opAt 2845 .ISZERO,
   pushAt 2846 2 4563,
   opAt 2847 .JUMPI]

/-- Instructions 3204..3209, pc 5247..4690. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2848 .JUMPDEST,
   pushAt 2849 2 8224,
   opAt 2850 .MLOAD,
   opAt 2851 .ISZERO,
   pushAt 2852 2 4759,
   opAt 2853 .JUMPI]

/-- Instructions 3210..3212, pc 4691..4695. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2854 0 0,
   pushAt 2855 2 9440,
   opAt 2856 .MLOAD]

/-- Instructions 3213..3244, pc 4696..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2857 .JUMPDEST,
   opAt 2858 (.Dup ⟨0, by decide⟩),
   opAt 2859 .MLOAD,
   opAt 2860 (.Dup ⟨1, by decide⟩),
   pushAt 2861 2 8256,
   opAt 2862 (.Swap ⟨0, by decide⟩),
   opAt 2863 .SUB,
   opAt 2864 .MLOAD,
   opAt 2865 (.Dup ⟨1, by decide⟩),
   opAt 2866 (.Dup ⟨1, by decide⟩),
   opAt 2867 .GT,
   opAt 2868 (.Swap ⟨1, by decide⟩),
   opAt 2869 .SUB,
   opAt 2870 (.Dup ⟨3, by decide⟩),
   opAt 2871 (.Dup ⟨1, by decide⟩),
   opAt 2872 .LT,
   opAt 2873 (.Swap ⟨0, by decide⟩),
   opAt 2874 (.Dup ⟨4, by decide⟩),
   opAt 2875 (.Swap ⟨0, by decide⟩),
   opAt 2876 .SUB,
   opAt 2877 (.Dup ⟨3, by decide⟩),
   opAt 2878 .MSTORE,
   opAt 2879 .OR,
   opAt 2880 (.Swap ⟨1, by decide⟩),
   opAt 2881 .POP,
   pushAt 2882 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2883 .ADD,
   pushAt 2884 2 8255,
   opAt 2885 (.Dup ⟨1, by decide⟩),
   opAt 2886 .GT,
   pushAt 2887 2 4675,
   opAt 2888 .JUMPI]

/-- Instructions 3245..3252, pc 4766..4779. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2889 .POP,
   pushAt 2890 2 8224,
   opAt 2891 .MLOAD,
   opAt 2892 .SUB,
   pushAt 2893 2 8224,
   opAt 2894 .MSTORE,
   pushAt 2895 2 4660,
   opAt 2896 .JUMP]

/-- Instructions 3253..3257, pc 4780..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2897 .JUMPDEST,
   pushAt 2898 2 4770,
   pushAt 2899 2 2048,
   pushAt 2900 2 2637,
   opAt 2901 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2902 .JUMPDEST,
   pushAt 2903 1 1,
   opAt 2904 (.Swap ⟨0, by decide⟩),
   opAt 2905 .SUB,
   pushAt 2906 2 4283,
   opAt 2907 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2908 .JUMPDEST,
   opAt 2909 .POP,
   pushAt 2910 2 1756,
   opAt 2911 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4052 = true :=
  Artifact.isValidJumpDest_index 2504 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4096 = true :=
  Artifact.isValidJumpDest_index 2531 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4101 = true :=
  Artifact.isValidJumpDest_index 2534 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4108 = true :=
  Artifact.isValidJumpDest_index 2538 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4169 = true :=
  Artifact.isValidJumpDest_index 2561 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4215 = true :=
  Artifact.isValidJumpDest_index 2598 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4246 = true :=
  Artifact.isValidJumpDest_index 2624 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4283 = true :=
  Artifact.isValidJumpDest_index 2655 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4304 = true :=
  Artifact.isValidJumpDest_index 2668 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4372 = true :=
  Artifact.isValidJumpDest_index 2718 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4386 = true :=
  Artifact.isValidJumpDest_index 2726 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4563 = true :=
  Artifact.isValidJumpDest_index 2797 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4569 = true :=
  Artifact.isValidJumpDest_index 2801 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4660 = true :=
  Artifact.isValidJumpDest_index 2848 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4675 = true :=
  Artifact.isValidJumpDest_index 2857 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4759 = true :=
  Artifact.isValidJumpDest_index 2897 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4770 = true :=
  Artifact.isValidJumpDest_index 2902 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4779 = true :=
  Artifact.isValidJumpDest_index 2908 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
