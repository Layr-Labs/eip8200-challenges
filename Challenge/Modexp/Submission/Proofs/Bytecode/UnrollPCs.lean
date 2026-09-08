import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The block holds eight byte-identical copies of the bit body.  Copy `k` starts
at instruction index `2365 + 17 * k` and at byte `3611 + 20 * k`; the entry
`JUMPDEST`, the `base - 1` it derives and the closing jump sit on either side
of the eight copies.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem pc484 : Artifact.submissionArtifact.instructionPC 484 = 606 := by rfl
@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 485 = 607 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 486 = 610 := by rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2548 = 3708 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2549 = 3709 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2550 = 3711 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2551 = 3712 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2552 = 3713 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2553 = 3714 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2554 = 3716 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2555 = 3717 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2556 = 3719 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2557 = 3720 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2558 = 3721 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2559 = 3722 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2560 = 3723 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2561 = 3725 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2562 = 3726 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2563 = 3727 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2564 = 3728 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2565 = 3729 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2566 = 3730 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2567 = 3731 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2568 = 3732 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2569 = 3733 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2570 = 3734 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2571 = 3736 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2572 = 3737 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2573 = 3739 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2574 = 3740 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2575 = 3741 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2576 = 3742 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2577 = 3743 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2578 = 3745 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2579 = 3746 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2580 = 3747 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2581 = 3748 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2582 = 3749 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2583 = 3750 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2584 = 3751 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2585 = 3752 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2586 = 3753 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2587 = 3754 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2588 = 3756 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2589 = 3757 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2590 = 3759 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2591 = 3760 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2592 = 3761 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2593 = 3762 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2594 = 3763 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2595 = 3765 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2596 = 3766 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2597 = 3767 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2598 = 3768 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2599 = 3769 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2600 = 3770 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2601 = 3771 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2602 = 3772 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2603 = 3773 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2604 = 3774 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2605 = 3776 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2606 = 3777 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2607 = 3779 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2608 = 3780 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2609 = 3781 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2610 = 3782 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2611 = 3783 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2612 = 3785 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2613 = 3786 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2614 = 3787 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2615 = 3788 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2616 = 3789 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2617 = 3790 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2618 = 3791 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2619 = 3792 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2620 = 3793 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2621 = 3794 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2622 = 3796 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2623 = 3797 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2624 = 3799 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2625 = 3800 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2626 = 3801 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2627 = 3802 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2628 = 3803 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2629 = 3805 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2630 = 3806 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2631 = 3807 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2632 = 3808 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2633 = 3809 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2634 = 3810 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2635 = 3811 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2636 = 3812 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2637 = 3813 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2638 = 3814 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2639 = 3816 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2640 = 3817 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2641 = 3819 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2642 = 3820 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2643 = 3821 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2644 = 3822 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2645 = 3823 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2646 = 3825 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2647 = 3826 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2648 = 3827 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2649 = 3828 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2650 = 3829 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2651 = 3830 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2652 = 3831 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2653 = 3832 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2654 = 3833 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2655 = 3834 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2656 = 3836 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2657 = 3837 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2658 = 3839 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2659 = 3840 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2660 = 3841 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2661 = 3842 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2662 = 3843 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2663 = 3845 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2664 = 3846 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2665 = 3847 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2666 = 3848 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2667 = 3849 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2668 = 3850 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2669 = 3851 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2670 = 3852 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2671 = 3853 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2672 = 3854 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2673 = 3856 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2674 = 3857 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2675 = 3859 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2676 = 3860 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2677 = 3861 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2678 = 3862 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2679 = 3863 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2680 = 3865 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2681 = 3866 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2682 = 3867 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2683 = 3868 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2684 = 3869 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2685 = 3870 := by rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2686 = 3871 := by rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2687 = 3872 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2688 = 3873 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2689 = 3874 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2690 = 3877 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
