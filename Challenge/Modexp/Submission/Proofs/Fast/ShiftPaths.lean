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
  [opAt 2488 .JUMPDEST,
   opAt 2489 (.Dup ⟨0, by decide⟩),
   opAt 2490 (.Dup ⟨3, by decide⟩),
   opAt 2491 .EQ,
   pushAt 2492 0 0,
   opAt 2493 .MLOAD,
   pushAt 2494 1 255,
   opAt 2495 .SHR,
   opAt 2496 .AND,
   opAt 2497 .ISZERO,
   pushAt 2498 2 4063,
   opAt 2499 .JUMPI]

/-- Instructions 2874..2888, pc 4092..4120. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2500 (.Dup ⟨0, by decide⟩),
   pushAt 2501 1 96,
   pushAt 2502 2 1024,
   opAt 2503 .CALLDATACOPY,
   opAt 2504 (.Dup ⟨0, by decide⟩),
   pushAt 2505 1 96,
   pushAt 2506 2 8256,
   opAt 2507 .CALLDATACOPY,
   pushAt 2508 0 0,
   pushAt 2509 2 8224,
   opAt 2510 .MSTORE,
   pushAt 2511 2 4068,
   pushAt 2512 2 2048,
   pushAt 2513 2 2610,
   opAt 2514 .JUMP]

/-- Instructions 2889..2891, pc 4687..4125. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2515 .JUMPDEST,
   pushAt 2516 2 1527,
   opAt 2517 .JUMP]

/-- Instructions 2892..2895, pc 4126..4698. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2518 .JUMPDEST,
   pushAt 2519 1 1,
   pushAt 2520 2 9408,
   opAt 2521 .MLOAD]

/-- Instructions 2896..2914, pc 4699..4721. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2522 .JUMPDEST,
   opAt 2523 (.Dup ⟨0, by decide⟩),
   opAt 2524 .MLOAD,
   opAt 2525 .NOT,
   opAt 2526 (.Dup ⟨2, by decide⟩),
   opAt 2527 .ADD,
   opAt 2528 (.Dup ⟨2, by decide⟩),
   opAt 2529 (.Dup ⟨1, by decide⟩),
   opAt 2530 .LT,
   opAt 2531 (.Swap ⟨2, by decide⟩),
   opAt 2532 .POP,
   opAt 2533 (.Dup ⟨1, by decide⟩),
   pushAt 2534 2 5120,
   opAt 2535 .ADD,
   opAt 2536 .MSTORE,
   opAt 2537 (.Dup ⟨0, by decide⟩),
   opAt 2538 .ISZERO,
   pushAt 2539 2 4136,
   opAt 2540 .JUMPI]

/-- Instructions 2915..2918, pc 4722..4193. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2541 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2542 .ADD,
   pushAt 2543 2 4075,
   opAt 2544 .JUMP]

/-- Instructions 2919..2955, pc 4194..4239. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2545 .JUMPDEST,
   opAt 2546 .POP,
   opAt 2547 .POP,
   pushAt 2548 0 0,
   opAt 2549 .MLOAD,
   opAt 2550 (.Dup ⟨0, by decide⟩),
   pushAt 2551 0 0,
   opAt 2552 .SUB,
   opAt 2553 (.Dup ⟨1, by decide⟩),
   opAt 2554 .AND,
   opAt 2555 (.Dup ⟨0, by decide⟩),
   pushAt 2556 2 6144,
   opAt 2557 .MSTORE,
   opAt 2558 (.Dup ⟨0, by decide⟩),
   opAt 2559 (.Dup ⟨2, by decide⟩),
   opAt 2560 .DIV,
   opAt 2561 (.Dup ⟨0, by decide⟩),
   pushAt 2562 2 6176,
   opAt 2563 .MSTORE,
   opAt 2564 (.Dup ⟨1, by decide⟩),
   pushAt 2565 0 0,
   opAt 2566 .SUB,
   opAt 2567 (.Dup ⟨2, by decide⟩),
   opAt 2568 (.Swap ⟨0, by decide⟩),
   opAt 2569 .DIV,
   pushAt 2570 1 1,
   opAt 2571 .ADD,
   pushAt 2572 2 6208,
   opAt 2573 .MSTORE,
   opAt 2574 (.Dup ⟨0, by decide⟩),
   pushAt 2575 0 0,
   opAt 2576 .SUB,
   opAt 2577 (.Dup ⟨1, by decide⟩),
   opAt 2578 (.Swap ⟨0, by decide⟩),
   opAt 2579 .MOD,
   pushAt 2580 2 6240,
   opAt 2581 .MSTORE]

/-- Instructions 2956..2981, pc 4240..4270. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   pushAt 2583 1 1,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   opAt 2585 (.Dup ⟨2, by decide⟩),
   opAt 2586 .MUL,
   pushAt 2587 1 2,
   opAt 2588 .SUB,
   opAt 2589 .MUL,
   opAt 2590 (.Dup ⟨0, by decide⟩),
   opAt 2591 (.Dup ⟨2, by decide⟩),
   opAt 2592 .MUL,
   pushAt 2593 1 2,
   opAt 2594 .SUB,
   opAt 2595 .MUL,
   opAt 2596 (.Dup ⟨0, by decide⟩),
   opAt 2597 (.Dup ⟨2, by decide⟩),
   opAt 2598 .MUL,
   pushAt 2599 1 2,
   opAt 2600 .SUB,
   opAt 2601 .MUL,
   opAt 2602 (.Dup ⟨0, by decide⟩),
   opAt 2603 (.Dup ⟨2, by decide⟩),
   opAt 2604 .MUL,
   pushAt 2605 1 2,
   opAt 2606 .SUB,
   opAt 2607 .MUL]

/-- Instructions 2982..3012, pc 4271..4873. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2608 .JUMPDEST,
   opAt 2609 (.Dup ⟨0, by decide⟩),
   opAt 2610 (.Dup ⟨2, by decide⟩),
   opAt 2611 .MUL,
   pushAt 2612 1 2,
   opAt 2613 .SUB,
   opAt 2614 .MUL,
   opAt 2615 (.Dup ⟨0, by decide⟩),
   opAt 2616 (.Dup ⟨2, by decide⟩),
   opAt 2617 .MUL,
   pushAt 2618 1 2,
   opAt 2619 .SUB,
   opAt 2620 .MUL,
   opAt 2621 (.Dup ⟨0, by decide⟩),
   opAt 2622 (.Dup ⟨2, by decide⟩),
   opAt 2623 .MUL,
   pushAt 2624 1 2,
   opAt 2625 .SUB,
   opAt 2626 .MUL,
   opAt 2627 (.Dup ⟨0, by decide⟩),
   opAt 2628 (.Dup ⟨2, by decide⟩),
   opAt 2629 .MUL,
   pushAt 2630 1 2,
   opAt 2631 .SUB,
   opAt 2632 .MUL,
   pushAt 2633 2 6272,
   opAt 2634 .MSTORE,
   opAt 2635 .POP,
   opAt 2636 .POP,
   opAt 2637 .POP,
   opAt 2638 (.Dup ⟨1, by decide⟩)]

/-- Instructions 3013..3017, pc 4308..4314. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2639 .JUMPDEST,
   opAt 2640 (.Dup ⟨0, by decide⟩),
   opAt 2641 .ISZERO,
   pushAt 2642 2 4745,
   opAt 2643 .JUMPI]

/-- Instructions 3018..3025, pc 4315..4328. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2644 (.Dup ⟨1, by decide⟩),
   pushAt 2645 2 2048,
   pushAt 2646 2 8224,
   opAt 2647 .MCOPY,
   pushAt 2648 0 0,
   pushAt 2649 2 9440,
   opAt 2650 .MLOAD,
   opAt 2651 .MSTORE]

/-- Instructions 3026..3068, pc 4895..4387. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2652 .JUMPDEST,
   pushAt 2653 2 2048,
   opAt 2654 .MLOAD,
   pushAt 2655 2 6144,
   opAt 2656 .MLOAD,
   opAt 2657 (.Dup ⟨1, by decide⟩),
   opAt 2658 (.Dup ⟨1, by decide⟩),
   opAt 2659 (.Swap ⟨0, by decide⟩),
   opAt 2660 .DIV,
   opAt 2661 (.Swap ⟨1, by decide⟩),
   opAt 2662 .MOD,
   pushAt 2663 2 6208,
   opAt 2664 .MLOAD,
   opAt 2665 .MUL,
   pushAt 2666 2 2080,
   opAt 2667 .MLOAD,
   pushAt 2668 2 6144,
   opAt 2669 .MLOAD,
   opAt 2670 (.Swap ⟨0, by decide⟩),
   opAt 2671 .DIV,
   opAt 2672 .ADD,
   pushAt 2673 2 6176,
   opAt 2674 .MLOAD,
   opAt 2675 (.Dup ⟨0, by decide⟩),
   pushAt 2676 2 6240,
   opAt 2677 .MLOAD,
   opAt 2678 (.Dup ⟨4, by decide⟩),
   opAt 2679 .MULMOD,
   opAt 2680 (.Dup ⟨2, by decide⟩),
   opAt 2681 (.Swap ⟨0, by decide⟩),
   opAt 2682 .ADDMOD,
   opAt 2683 (.Swap ⟨0, by decide⟩),
   opAt 2684 .SUB,
   pushAt 2685 2 6272,
   opAt 2686 .MLOAD,
   opAt 2687 .MUL,
   opAt 2688 (.Dup ⟨0, by decide⟩),
   pushAt 2689 0 0,
   opAt 2690 .LT,
   opAt 2691 (.Swap ⟨0, by decide⟩),
   opAt 2692 .SUB,
   opAt 2693 (.Swap ⟨0, by decide⟩),
   pushAt 2694 2 6176,
   opAt 2695 .MLOAD,
      opAt 2696 .GT,
   opAt 2697 .ISZERO,
   pushAt 2698 0 0,
   opAt 2699 .SUB,
   opAt 2700 .OR]

/-- Instructions 3069..3076, pc 4388..4967. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2701 .JUMPDEST,
   pushAt 2702 0 0,
   pushAt 2703 2 9440,
   opAt 2704 .MLOAD,
   pushAt 2705 2 9408,
   opAt 2706 .MLOAD,
   pushAt 2707 2 5120,
   opAt 2708 .ADD]

/-- Instructions 3077..3124, pc 4968..4549. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2709 .JUMPDEST,
   opAt 2710 (.Dup ⟨0, by decide⟩),
   opAt 2711 .MLOAD,
   pushAt 2712 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2713 (.Dup ⟨5, by decide⟩),
   opAt 2714 (.Dup ⟨2, by decide⟩),
   opAt 2715 .MUL,
   opAt 2716 (.Swap ⟨1, by decide⟩),
   opAt 2717 (.Dup ⟨6, by decide⟩),
   opAt 2718 .MULMOD,
   opAt 2719 (.Dup ⟨1, by decide⟩),
   opAt 2720 (.Dup ⟨1, by decide⟩),
   opAt 2721 .LT,
   opAt 2722 .SUB,
   opAt 2723 (.Dup ⟨4, by decide⟩),
   opAt 2724 (.Dup ⟨2, by decide⟩),
   opAt 2725 .ADD,
   opAt 2726 (.Dup ⟨0, by decide⟩),
   opAt 2727 (.Swap ⟨5, by decide⟩),
   opAt 2728 .GT,
   opAt 2729 .SUB,
   opAt 2730 .SUB,
   opAt 2731 (.Dup ⟨3, by decide⟩),
   opAt 2732 (.Dup ⟨3, by decide⟩),
   opAt 2733 .MLOAD,
   opAt 2734 .ADD,
   opAt 2735 (.Dup ⟨0, by decide⟩),
   opAt 2736 (.Swap ⟨4, by decide⟩),
   opAt 2737 .GT,
   opAt 2738 .ADD,
   opAt 2739 (.Swap ⟨2, by decide⟩),
   opAt 2740 (.Dup ⟨2, by decide⟩),
   pushAt 2741 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2742 .ADD,
   opAt 2743 (.Swap ⟨2, by decide⟩),
   opAt 2744 .MSTORE,
   pushAt 2745 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2746 .ADD,
   pushAt 2747 2 8224,
   opAt 2748 (.Dup ⟨2, by decide⟩),
   opAt 2749 .GT,
   pushAt 2750 2 4352,
   opAt 2751 .JUMPI]

/-- Instructions 3125..3152, pc 4550..4583. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2752 .POP,
   opAt 2753 .POP,
   pushAt 2754 2 8224,
   opAt 2755 .MLOAD,
   opAt 2756 (.Dup ⟨1, by decide⟩),
   opAt 2757 .ADD,
   opAt 2758 (.Dup ⟨1, by decide⟩),
   opAt 2759 (.Dup ⟨1, by decide⟩),
   opAt 2760 .LT,
   opAt 2761 (.Swap ⟨1, by decide⟩),
   opAt 2762 .POP,
   opAt 2763 (.Dup ⟨2, by decide⟩),
   opAt 2764 (.Dup ⟨1, by decide⟩),
   opAt 2765 .LT,
   opAt 2766 (.Swap ⟨0, by decide⟩),
   opAt 2767 (.Dup ⟨3, by decide⟩),
   opAt 2768 (.Swap ⟨0, by decide⟩),
   opAt 2769 .SUB,
   opAt 2770 (.Dup ⟨0, by decide⟩),
   pushAt 2771 2 8224,
   opAt 2772 .MSTORE,
   opAt 2773 .POP,
   opAt 2774 .GT,
   opAt 2775 (.Swap ⟨0, by decide⟩),
   opAt 2776 .POP,
   opAt 2777 .ISZERO,
   pushAt 2778 2 4626,
   opAt 2779 .JUMPI]

/-- Instructions 3153..3156, pc 4584..4589. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2780 .JUMPDEST,
   pushAt 2781 0 0,
   pushAt 2782 2 9440,
   opAt 2783 .MLOAD]

/-- Instructions 3157..3191, pc 4590..5228. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2784 .JUMPDEST,
   opAt 2785 (.Dup ⟨0, by decide⟩),
   opAt 2786 .MLOAD,
   opAt 2787 (.Dup ⟨1, by decide⟩),
   pushAt 2788 2 8256,
   opAt 2789 (.Swap ⟨0, by decide⟩),
   opAt 2790 .SUB,
   opAt 2791 .MLOAD,
   opAt 2792 (.Dup ⟨1, by decide⟩),
   opAt 2793 .ADD,
   opAt 2794 (.Dup ⟨0, by decide⟩),
   opAt 2795 (.Dup ⟨2, by decide⟩),
   opAt 2796 .GT,
   opAt 2797 (.Swap ⟨1, by decide⟩),
   opAt 2798 .POP,
   opAt 2799 (.Dup ⟨3, by decide⟩),
   opAt 2800 .ADD,
   opAt 2801 (.Dup ⟨0, by decide⟩),
   opAt 2802 (.Dup ⟨4, by decide⟩),
   opAt 2803 .GT,
   opAt 2804 (.Swap ⟨3, by decide⟩),
   opAt 2805 .POP,
   opAt 2806 (.Dup ⟨2, by decide⟩),
   opAt 2807 .MSTORE,
   opAt 2808 (.Swap ⟨0, by decide⟩),
   opAt 2809 (.Swap ⟨1, by decide⟩),
   opAt 2810 .OR,
   opAt 2811 (.Swap ⟨0, by decide⟩),
   pushAt 2812 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2813 .ADD,
   pushAt 2814 2 8255,
   opAt 2815 (.Dup ⟨1, by decide⟩),
   opAt 2816 .GT,
   pushAt 2817 2 4535,
   opAt 2818 .JUMPI]

/-- Instructions 3192..3203, pc 5229..5246. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2819 .POP,
   pushAt 2820 2 8224,
   opAt 2821 .MLOAD,
   opAt 2822 (.Dup ⟨1, by decide⟩),
   opAt 2823 .ADD,
   opAt 2824 (.Dup ⟨0, by decide⟩),
   pushAt 2825 2 8224,
   opAt 2826 .MSTORE,
   opAt 2827 .LT,
   opAt 2828 .ISZERO,
   pushAt 2829 2 4529,
   opAt 2830 .JUMPI]

/-- Instructions 3204..3209, pc 5247..4690. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2831 .JUMPDEST,
   pushAt 2832 2 8224,
   opAt 2833 .MLOAD,
   opAt 2834 .ISZERO,
   pushAt 2835 2 4725,
   opAt 2836 .JUMPI]

/-- Instructions 3210..3212, pc 4691..4695. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2837 0 0,
   pushAt 2838 2 9440,
   opAt 2839 .MLOAD]

/-- Instructions 3213..3244, pc 4696..5331. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2840 .JUMPDEST,
   opAt 2841 (.Dup ⟨0, by decide⟩),
   opAt 2842 .MLOAD,
   opAt 2843 (.Dup ⟨1, by decide⟩),
   pushAt 2844 2 8256,
   opAt 2845 (.Swap ⟨0, by decide⟩),
   opAt 2846 .SUB,
   opAt 2847 .MLOAD,
   opAt 2848 (.Dup ⟨1, by decide⟩),
   opAt 2849 (.Dup ⟨1, by decide⟩),
   opAt 2850 .GT,
   opAt 2851 (.Swap ⟨1, by decide⟩),
   opAt 2852 .SUB,
   opAt 2853 (.Dup ⟨3, by decide⟩),
   opAt 2854 (.Dup ⟨1, by decide⟩),
   opAt 2855 .LT,
   opAt 2856 (.Swap ⟨0, by decide⟩),
   opAt 2857 (.Dup ⟨4, by decide⟩),
   opAt 2858 (.Swap ⟨0, by decide⟩),
   opAt 2859 .SUB,
   opAt 2860 (.Dup ⟨3, by decide⟩),
   opAt 2861 .MSTORE,
   opAt 2862 .OR,
   opAt 2863 (.Swap ⟨1, by decide⟩),
   opAt 2864 .POP,
   pushAt 2865 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2866 .ADD,
   pushAt 2867 2 8255,
   opAt 2868 (.Dup ⟨1, by decide⟩),
   opAt 2869 .GT,
   pushAt 2870 2 4641,
   opAt 2871 .JUMPI]

/-- Instructions 3245..3252, pc 4766..4779. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2872 .POP,
   pushAt 2873 2 8224,
   opAt 2874 .MLOAD,
   opAt 2875 .SUB,
   pushAt 2876 2 8224,
   opAt 2877 .MSTORE,
   pushAt 2878 2 4626,
   opAt 2879 .JUMP]

/-- Instructions 3253..3257, pc 4780..5356. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2880 .JUMPDEST,
   pushAt 2881 2 4736,
   pushAt 2882 2 2048,
   pushAt 2883 2 2610,
   opAt 2884 .JUMP]

/-- Instructions 3258..3263, pc 5357..5365. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2885 .JUMPDEST,
   pushAt 2886 1 1,
   opAt 2887 (.Swap ⟨0, by decide⟩),
   opAt 2888 .SUB,
   pushAt 2889 2 4250,
   opAt 2890 .JUMP]

/-- Instructions 3264..3267, pc 5366..5371. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2891 .JUMPDEST,
   opAt 2892 .POP,
   pushAt 2893 2 1737,
   opAt 2894 .JUMP]

theorem jumpDest4643 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4019 = true :=
  Artifact.isValidJumpDest_index 2488 (by rfl)

theorem jumpDest4687 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4063 = true :=
  Artifact.isValidJumpDest_index 2515 (by rfl)

theorem jumpDest4692 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4068 = true :=
  Artifact.isValidJumpDest_index 2518 (by rfl)

theorem jumpDest4699 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4075 = true :=
  Artifact.isValidJumpDest_index 2522 (by rfl)

theorem jumpDest4760 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4136 = true :=
  Artifact.isValidJumpDest_index 2545 (by rfl)

theorem jumpDest4806 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4182 = true :=
  Artifact.isValidJumpDest_index 2582 (by rfl)

theorem jumpDest4837 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4213 = true :=
  Artifact.isValidJumpDest_index 2608 (by rfl)

theorem jumpDest4874 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4250 = true :=
  Artifact.isValidJumpDest_index 2639 (by rfl)

theorem jumpDest4895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4271 = true :=
  Artifact.isValidJumpDest_index 2652 (by rfl)

theorem jumpDest4954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4338 = true :=
  Artifact.isValidJumpDest_index 2701 (by rfl)

theorem jumpDest4968 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4352 = true :=
  Artifact.isValidJumpDest_index 2709 (by rfl)

theorem jumpDest5150 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4529 = true :=
  Artifact.isValidJumpDest_index 2780 (by rfl)

theorem jumpDest5156 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4535 = true :=
  Artifact.isValidJumpDest_index 2784 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4626 = true :=
  Artifact.isValidJumpDest_index 2831 (by rfl)

theorem jumpDest5262 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4641 = true :=
  Artifact.isValidJumpDest_index 2840 (by rfl)

theorem jumpDest5346 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4725 = true :=
  Artifact.isValidJumpDest_index 2880 (by rfl)

theorem jumpDest5357 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4736 = true :=
  Artifact.isValidJumpDest_index 2885 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4745 = true :=
  Artifact.isValidJumpDest_index 2891 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
