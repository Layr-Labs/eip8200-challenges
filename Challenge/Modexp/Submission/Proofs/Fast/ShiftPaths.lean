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
  [opAt 2425 .JUMPDEST,
   opAt 2426 (.Dup ⟨0, by decide⟩),
   opAt 2427 (.Dup ⟨3, by decide⟩),
   opAt 2428 .EQ,
   pushAt 2429 0 0,
   opAt 2430 .MLOAD,
   pushAt 2431 1 255,
   opAt 2432 .SHR,
   opAt 2433 .AND,
   opAt 2434 .ISZERO,
   pushAt 2435 2 3213,
   opAt 2436 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2437 (.Dup ⟨0, by decide⟩),
   pushAt 2438 1 96,
   pushAt 2439 2 1024,
   opAt 2440 .CALLDATACOPY,
   opAt 2441 (.Dup ⟨0, by decide⟩),
   pushAt 2442 1 96,
   pushAt 2443 2 8256,
   opAt 2444 .CALLDATACOPY,
   pushAt 2445 0 0,
   pushAt 2446 2 8224,
   opAt 2447 .MSTORE,
   pushAt 2448 2 3230,
   pushAt 2449 2 2048,
   pushAt 2450 2 4536,
   opAt 2451 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2452 .JUMPDEST,
   pushAt 2453 1 1,
   pushAt 2454 2 4096,
   opAt 2455 .MSTORE,
   pushAt 2456 2 1167,
   pushAt 2457 2 4096,
   pushAt 2458 2 1948,
   opAt 2459 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2460 .JUMPDEST,
   pushAt 2461 1 1,
   pushAt 2462 2 9408,
   opAt 2463 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2896 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2464 .JUMPDEST,
   opAt 2465 (.Dup ⟨0, by decide⟩),
   opAt 2466 .MLOAD,
   opAt 2467 .NOT,
   opAt 2468 (.Dup ⟨2, by decide⟩),
   opAt 2469 .ADD,
   opAt 2470 (.Dup ⟨2, by decide⟩),
   opAt 2471 (.Dup ⟨1, by decide⟩),
   opAt 2472 .LT,
   opAt 2473 (.Swap ⟨2, by decide⟩),
   opAt 2474 .POP,
   opAt 2475 (.Dup ⟨1, by decide⟩),
   pushAt 2476 2 5120,
   opAt 2477 .ADD,
   opAt 2478 .MSTORE,
   opAt 2479 (.Dup ⟨0, by decide⟩),
   opAt 2480 .ISZERO,
   pushAt 2481 2 3268,
   opAt 2482 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2915 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2483 1 31,
   opAt 2484 .NOT,
   opAt 2485 .ADD,
   pushAt 2486 2 3237,
   opAt 2487 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2488 .JUMPDEST,
   opAt 2489 .POP,
   opAt 2490 .POP,
   pushAt 2491 0 0,
   opAt 2492 .MLOAD,
   opAt 2493 (.Dup ⟨0, by decide⟩),
   pushAt 2494 0 0,
   opAt 2495 .SUB,
   opAt 2496 (.Dup ⟨1, by decide⟩),
   opAt 2497 .AND,
   opAt 2498 (.Dup ⟨0, by decide⟩),
   pushAt 2499 2 6144,
   opAt 2500 .MSTORE,
   opAt 2501 (.Dup ⟨0, by decide⟩),
   opAt 2502 (.Dup ⟨2, by decide⟩),
   opAt 2503 .DIV,
   opAt 2504 (.Dup ⟨0, by decide⟩),
   pushAt 2505 2 6176,
   opAt 2506 .MSTORE,
   opAt 2507 (.Dup ⟨1, by decide⟩),
   pushAt 2508 0 0,
   opAt 2509 .SUB,
   opAt 2510 (.Dup ⟨2, by decide⟩),
   opAt 2511 (.Swap ⟨0, by decide⟩),
   opAt 2512 .DIV,
   pushAt 2513 1 1,
   opAt 2514 .ADD,
   pushAt 2515 2 6208,
   opAt 2516 .MSTORE,
   opAt 2517 (.Dup ⟨0, by decide⟩),
   pushAt 2518 0 0,
   opAt 2519 .SUB,
   opAt 2520 (.Dup ⟨1, by decide⟩),
   opAt 2521 (.Swap ⟨0, by decide⟩),
   opAt 2522 .MOD,
   pushAt 2523 2 6240,
   opAt 2524 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2525 (.Dup ⟨0, by decide⟩),
   pushAt 2526 1 2,
   opAt 2527 .SUB,
   opAt 2528 (.Dup ⟨0, by decide⟩),
   opAt 2529 (.Dup ⟨2, by decide⟩),
   opAt 2530 .MUL,
   pushAt 2531 1 2,
   opAt 2532 .SUB,
   opAt 2533 .MUL,
   opAt 2534 (.Dup ⟨0, by decide⟩),
   opAt 2535 (.Dup ⟨2, by decide⟩),
   opAt 2536 .MUL,
   pushAt 2537 1 2,
   opAt 2538 .SUB,
   opAt 2539 .MUL,
   opAt 2540 (.Dup ⟨0, by decide⟩),
   opAt 2541 (.Dup ⟨2, by decide⟩),
   opAt 2542 .MUL,
   pushAt 2543 1 2,
   opAt 2544 .SUB,
   opAt 2545 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2546 (.Dup ⟨0, by decide⟩),
   opAt 2547 (.Dup ⟨2, by decide⟩),
   opAt 2548 .MUL,
   pushAt 2549 1 2,
   opAt 2550 .SUB,
   opAt 2551 .MUL,
   opAt 2552 (.Dup ⟨0, by decide⟩),
   opAt 2553 (.Dup ⟨2, by decide⟩),
   opAt 2554 .MUL,
   pushAt 2555 1 2,
   opAt 2556 .SUB,
   opAt 2557 .MUL,
   opAt 2558 (.Dup ⟨0, by decide⟩),
   opAt 2559 (.Dup ⟨2, by decide⟩),
   opAt 2560 .MUL,
   pushAt 2561 1 2,
   opAt 2562 .SUB,
   opAt 2563 .MUL,
   opAt 2564 (.Dup ⟨0, by decide⟩),
   opAt 2565 (.Dup ⟨2, by decide⟩),
   opAt 2566 .MUL,
   pushAt 2567 1 2,
   opAt 2568 .SUB,
   opAt 2569 .MUL,
   pushAt 2570 2 6272,
   opAt 2571 .MSTORE,
   opAt 2572 .POP,
   opAt 2573 .POP,
   opAt 2574 .POP,
   opAt 2575 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2576 .JUMPDEST,
   opAt 2577 (.Dup ⟨0, by decide⟩),
   opAt 2578 .ISZERO,
   pushAt 2579 2 3762,
   opAt 2580 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2581 (.Dup ⟨1, by decide⟩),
   pushAt 2582 2 2048,
   pushAt 2583 2 8224,
   opAt 2584 .MCOPY,
   pushAt 2585 0 0,
   pushAt 2586 2 9440,
   opAt 2587 .MLOAD,
   opAt 2588 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2589 2 2048,
   opAt 2590 .MLOAD,
   pushAt 2591 2 6144,
   opAt 2592 .MLOAD,
   opAt 2593 (.Dup ⟨0, by decide⟩),
   opAt 2594 (.Dup ⟨2, by decide⟩),
   opAt 2595 .DIV,
   opAt 2596 (.Swap ⟨1, by decide⟩),
   opAt 2597 .MOD,
   pushAt 2598 2 6208,
   opAt 2599 .MLOAD,
   opAt 2600 .MUL,
   pushAt 2601 2 2080,
   opAt 2602 .MLOAD,
   pushAt 2603 2 6144,
   opAt 2604 .MLOAD,
   opAt 2605 (.Swap ⟨0, by decide⟩),
   opAt 2606 .DIV,
   opAt 2607 .ADD,
   pushAt 2608 2 6176,
   opAt 2609 .MLOAD,
   opAt 2610 (.Dup ⟨0, by decide⟩),
   pushAt 2611 2 6240,
   opAt 2612 .MLOAD,
   opAt 2613 (.Dup ⟨4, by decide⟩),
   opAt 2614 .MULMOD,
   opAt 2615 (.Dup ⟨2, by decide⟩),
   opAt 2616 .ADDMOD,
   opAt 2617 (.Swap ⟨0, by decide⟩),
   opAt 2618 .SUB,
   pushAt 2619 2 6272,
   opAt 2620 .MLOAD,
   opAt 2621 .MUL,
   opAt 2622 (.Dup ⟨0, by decide⟩),
   pushAt 2623 0 0,
   opAt 2624 .MLOAD,
   opAt 2625 .MUL,
   pushAt 2626 2 2080,
   opAt 2627 .MLOAD,
   opAt 2628 .SUB,
   pushAt 2629 1 32,
   opAt 2630 .MLOAD,
   pushAt 2631 1 128,
   opAt 2632 .SHR,
   opAt 2633 (.Dup ⟨2, by decide⟩),
   pushAt 2634 1 128,
   opAt 2635 .SHR,
   opAt 2636 .MUL,
   opAt 2637 .GT,
   opAt 2638 (.Swap ⟨0, by decide⟩),
   opAt 2639 .SUB,
   opAt 2640 (.Swap ⟨0, by decide⟩),
   pushAt 2641 2 6176,
   opAt 2642 .MLOAD,
   opAt 2643 .GT,
   opAt 2644 .ISZERO,
   pushAt 2645 0 0,
   opAt 2646 .SUB,
   opAt 2647 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2648 0 0,
   pushAt 2649 2 9440,
   opAt 2650 .MLOAD,
   pushAt 2651 2 9408,
   opAt 2652 .MLOAD,
   pushAt 2653 2 5120,
   opAt 2654 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2655 .JUMPDEST,
   opAt 2656 (.Dup ⟨0, by decide⟩),
   opAt 2657 .MLOAD,
   pushAt 2658 0 0,
   opAt 2659 .NOT,
   opAt 2660 (.Dup ⟨5, by decide⟩),
   opAt 2661 (.Dup ⟨2, by decide⟩),
   opAt 2662 .MUL,
   opAt 2663 (.Swap ⟨1, by decide⟩),
   opAt 2664 (.Dup ⟨6, by decide⟩),
   opAt 2665 .MULMOD,
   opAt 2666 (.Dup ⟨1, by decide⟩),
   opAt 2667 (.Dup ⟨1, by decide⟩),
   opAt 2668 .LT,
   opAt 2669 .SUB,
   opAt 2670 (.Dup ⟨4, by decide⟩),
   opAt 2671 (.Dup ⟨2, by decide⟩),
   opAt 2672 .ADD,
   opAt 2673 (.Dup ⟨0, by decide⟩),
   opAt 2674 (.Swap ⟨5, by decide⟩),
   opAt 2675 .GT,
   opAt 2676 .SUB,
   opAt 2677 .SUB,
   opAt 2678 (.Dup ⟨3, by decide⟩),
   opAt 2679 (.Dup ⟨3, by decide⟩),
   opAt 2680 .MLOAD,
   opAt 2681 .ADD,
   opAt 2682 (.Dup ⟨0, by decide⟩),
   opAt 2683 (.Swap ⟨4, by decide⟩),
   opAt 2684 .GT,
   opAt 2685 .ADD,
   opAt 2686 (.Swap ⟨2, by decide⟩),
   opAt 2687 (.Dup ⟨2, by decide⟩),
   pushAt 2688 1 31,
   opAt 2689 .NOT,
   opAt 2690 .ADD,
   opAt 2691 (.Swap ⟨2, by decide⟩),
   opAt 2692 .MSTORE,
   pushAt 2693 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2694 .ADD,
   pushAt 2695 2 8224,
   opAt 2696 (.Dup ⟨2, by decide⟩),
   opAt 2697 .GT,
   pushAt 2698 2 3491,
   opAt 2699 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2700 .POP,
   opAt 2701 .POP,
   pushAt 2702 2 8224,
   opAt 2703 .MLOAD,
   opAt 2704 (.Dup ⟨1, by decide⟩),
   opAt 2705 .ADD,
   opAt 2706 (.Dup ⟨1, by decide⟩),
   opAt 2707 (.Dup ⟨1, by decide⟩),
   opAt 2708 .LT,
   opAt 2709 (.Swap ⟨1, by decide⟩),
   opAt 2710 .POP,
   opAt 2711 (.Dup ⟨2, by decide⟩),
   opAt 2712 (.Dup ⟨1, by decide⟩),
   opAt 2713 .LT,
   opAt 2714 (.Swap ⟨0, by decide⟩),
   opAt 2715 (.Dup ⟨3, by decide⟩),
   opAt 2716 (.Swap ⟨0, by decide⟩),
   opAt 2717 .SUB,
   opAt 2718 (.Dup ⟨0, by decide⟩),
   pushAt 2719 2 8224,
   opAt 2720 .MSTORE,
   opAt 2721 .POP,
   opAt 2722 .GT,
   opAt 2723 (.Swap ⟨0, by decide⟩),
   opAt 2724 .POP,
   opAt 2725 .ISZERO,
   pushAt 2726 2 3674,
   opAt 2727 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2728 .JUMPDEST,
   pushAt 2729 0 0,
   pushAt 2730 2 9440,
   opAt 2731 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2732 .JUMPDEST,
   opAt 2733 (.Dup ⟨0, by decide⟩),
   opAt 2734 .MLOAD,
   opAt 2735 (.Dup ⟨1, by decide⟩),
   pushAt 2736 2 8256,
   opAt 2737 (.Swap ⟨0, by decide⟩),
   opAt 2738 .SUB,
   opAt 2739 .MLOAD,
   opAt 2740 (.Dup ⟨1, by decide⟩),
   opAt 2741 .ADD,
   opAt 2742 (.Dup ⟨0, by decide⟩),
   opAt 2743 (.Dup ⟨2, by decide⟩),
   opAt 2744 .GT,
   opAt 2745 (.Swap ⟨1, by decide⟩),
   opAt 2746 .POP,
   opAt 2747 (.Dup ⟨3, by decide⟩),
   opAt 2748 .ADD,
   opAt 2749 (.Dup ⟨0, by decide⟩),
   opAt 2750 (.Dup ⟨4, by decide⟩),
   opAt 2751 .GT,
   opAt 2752 (.Swap ⟨3, by decide⟩),
   opAt 2753 .POP,
   opAt 2754 (.Dup ⟨2, by decide⟩),
   opAt 2755 .MSTORE,
   opAt 2756 (.Swap ⟨0, by decide⟩),
   opAt 2757 (.Swap ⟨1, by decide⟩),
   opAt 2758 .OR,
   opAt 2759 (.Swap ⟨0, by decide⟩),
   pushAt 2760 1 31,
   opAt 2761 .NOT,
   opAt 2762 .ADD,
   pushAt 2763 2 8255,
   opAt 2764 (.Dup ⟨1, by decide⟩),
   opAt 2765 .GT,
   pushAt 2766 2 3613,
   opAt 2767 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2768 .POP,
   pushAt 2769 2 8224,
   opAt 2770 .MLOAD,
   opAt 2771 (.Dup ⟨1, by decide⟩),
   opAt 2772 .ADD,
   opAt 2773 (.Dup ⟨0, by decide⟩),
   pushAt 2774 2 8224,
   opAt 2775 .MSTORE,
   opAt 2776 .LT,
   opAt 2777 .ISZERO,
   pushAt 2778 2 3607,
   opAt 2779 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2780 .JUMPDEST,
   pushAt 2781 2 8224,
   opAt 2782 .MLOAD,
   opAt 2783 .ISZERO,
   pushAt 2784 2 3742,
   opAt 2785 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2786 0 0,
   pushAt 2787 2 9440,
   opAt 2788 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2789 .JUMPDEST,
   opAt 2790 (.Dup ⟨0, by decide⟩),
   opAt 2791 .MLOAD,
   pushAt 2792 2 8256,
   opAt 2793 (.Dup ⟨2, by decide⟩),
   opAt 2794 .SUB,
   opAt 2795 .MLOAD,
   opAt 2796 (.Dup ⟨1, by decide⟩),
   opAt 2797 (.Dup ⟨1, by decide⟩),
   opAt 2798 .GT,
   opAt 2799 (.Swap ⟨1, by decide⟩),
   opAt 2800 .SUB,
   opAt 2801 (.Dup ⟨3, by decide⟩),
   opAt 2802 (.Dup ⟨1, by decide⟩),
   opAt 2803 .LT,
   opAt 2804 (.Swap ⟨0, by decide⟩),
   opAt 2805 (.Dup ⟨4, by decide⟩),
   opAt 2806 (.Swap ⟨0, by decide⟩),
   opAt 2807 .SUB,
   opAt 2808 (.Dup ⟨3, by decide⟩),
   opAt 2809 .MSTORE,
   opAt 2810 .OR,
   opAt 2811 (.Swap ⟨1, by decide⟩),
   opAt 2812 .POP,
   pushAt 2813 1 31,
   opAt 2814 .NOT,
   opAt 2815 .ADD,
   pushAt 2816 2 8255,
   opAt 2817 (.Dup ⟨1, by decide⟩),
   opAt 2818 .GT,
   pushAt 2819 2 3689,
   opAt 2820 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2821 .POP,
   pushAt 2822 2 8224,
   opAt 2823 .MLOAD,
   opAt 2824 .SUB,
   pushAt 2825 2 8224,
   opAt 2826 .MSTORE,
   pushAt 2827 2 3674,
   opAt 2828 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2829 .JUMPDEST,
   pushAt 2830 2 3753,
   pushAt 2831 2 2048,
   pushAt 2832 2 4536,
   opAt 2833 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3258 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2834 .JUMPDEST,
   pushAt 2835 0 0,
   opAt 2836 .NOT,
   opAt 2837 .ADD,
   pushAt 2838 3 3375,
   opAt 2839 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2840 .JUMPDEST,
   opAt 2841 .POP,
   pushAt 2842 2 9344,
   opAt 2843 .MLOAD,
   pushAt 2844 2 5120,
   pushAt 2845 2 4096,
   opAt 2846 .MCOPY,
   pushAt 2847 2 3005,
   opAt 2848 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3169 = true :=
  Artifact.isValidJumpDest_index 2425 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3213 = true :=
  Artifact.isValidJumpDest_index 2452 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3230 = true :=
  Artifact.isValidJumpDest_index 2460 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3237 = true :=
  Artifact.isValidJumpDest_index 2464 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3268 = true :=
  Artifact.isValidJumpDest_index 2488 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3375 = true :=
  Artifact.isValidJumpDest_index 2576 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3491 = true :=
  Artifact.isValidJumpDest_index 2655 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3607 = true :=
  Artifact.isValidJumpDest_index 2728 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3613 = true :=
  Artifact.isValidJumpDest_index 2732 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3674 = true :=
  Artifact.isValidJumpDest_index 2780 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3689 = true :=
  Artifact.isValidJumpDest_index 2789 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3742 = true :=
  Artifact.isValidJumpDest_index 2829 (by rfl)

theorem jumpDest5322 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3753 = true :=
  Artifact.isValidJumpDest_index 2834 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3762 = true :=
  Artifact.isValidJumpDest_index 2840 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
