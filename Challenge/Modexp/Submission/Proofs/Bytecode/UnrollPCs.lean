import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The block holds eight byte-identical copies of the bit body.  Copy `k` starts
at instruction index `2443 + 17 * k` and at byte `3729 + 20 * k`; the entry
`JUMPDEST`, the `base - 1` it derives and the closing jump sit on either side
of the eight copies.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem pc484 : Artifact.submissionArtifact.instructionPC 484 = 606 := by rfl
@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 485 = 607 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 486 = 610 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2439 = 3724 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2440 = 3725 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2441 = 3727 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2442 = 3728 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2443 = 3729 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2444 = 3730 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2445 = 3732 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2446 = 3733 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2447 = 3735 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2448 = 3736 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2449 = 3737 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2450 = 3738 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2451 = 3739 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2452 = 3741 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2453 = 3742 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2454 = 3743 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2455 = 3744 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2456 = 3745 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2457 = 3746 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2458 = 3747 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2459 = 3748 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2460 = 3749 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2461 = 3750 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2462 = 3752 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2463 = 3753 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2464 = 3755 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2465 = 3756 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2466 = 3757 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2467 = 3758 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2468 = 3759 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2469 = 3761 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2470 = 3762 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2471 = 3763 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2472 = 3764 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2473 = 3765 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2474 = 3766 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2475 = 3767 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2476 = 3768 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2477 = 3769 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2478 = 3770 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2479 = 3772 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2480 = 3773 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2481 = 3775 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2482 = 3776 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2483 = 3777 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2484 = 3778 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2485 = 3779 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2486 = 3781 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2487 = 3782 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2488 = 3783 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2489 = 3784 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2490 = 3785 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2491 = 3786 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2492 = 3787 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2493 = 3788 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2494 = 3789 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2495 = 3790 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2496 = 3792 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2497 = 3793 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2498 = 3795 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2499 = 3796 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2500 = 3797 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2501 = 3798 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2502 = 3799 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2503 = 3801 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2504 = 3802 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2505 = 3803 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2506 = 3804 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2507 = 3805 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2508 = 3806 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2509 = 3807 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2510 = 3808 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2511 = 3809 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2512 = 3810 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2513 = 3812 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2514 = 3813 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2515 = 3815 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2516 = 3816 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2517 = 3817 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2518 = 3818 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2519 = 3819 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2520 = 3821 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2521 = 3822 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2522 = 3823 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2523 = 3824 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2524 = 3825 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2525 = 3826 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2526 = 3827 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2527 = 3828 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2528 = 3829 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2529 = 3830 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2530 = 3832 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2531 = 3833 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2532 = 3835 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2533 = 3836 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2534 = 3837 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2535 = 3838 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2536 = 3839 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2537 = 3841 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2538 = 3842 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2539 = 3843 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2540 = 3844 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2541 = 3845 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2542 = 3846 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2543 = 3847 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2544 = 3848 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2545 = 3849 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2546 = 3850 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2547 = 3852 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2548 = 3853 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2549 = 3855 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2550 = 3856 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2551 = 3857 := by rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2552 = 3858 := by rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2553 = 3859 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2554 = 3861 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2555 = 3862 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2556 = 3863 := by rfl
@[simp] theorem pc2557 : Artifact.submissionArtifact.instructionPC 2557 = 3864 := by rfl
@[simp] theorem pc2558 : Artifact.submissionArtifact.instructionPC 2558 = 3865 := by rfl
@[simp] theorem pc2559 : Artifact.submissionArtifact.instructionPC 2559 = 3866 := by rfl
@[simp] theorem pc2560 : Artifact.submissionArtifact.instructionPC 2560 = 3867 := by rfl
@[simp] theorem pc2561 : Artifact.submissionArtifact.instructionPC 2561 = 3868 := by rfl
@[simp] theorem pc2562 : Artifact.submissionArtifact.instructionPC 2562 = 3869 := by rfl
@[simp] theorem pc2563 : Artifact.submissionArtifact.instructionPC 2563 = 3870 := by rfl
@[simp] theorem pc2564 : Artifact.submissionArtifact.instructionPC 2564 = 3872 := by rfl
@[simp] theorem pc2565 : Artifact.submissionArtifact.instructionPC 2565 = 3873 := by rfl
@[simp] theorem pc2566 : Artifact.submissionArtifact.instructionPC 2566 = 3875 := by rfl
@[simp] theorem pc2567 : Artifact.submissionArtifact.instructionPC 2567 = 3876 := by rfl
@[simp] theorem pc2568 : Artifact.submissionArtifact.instructionPC 2568 = 3877 := by rfl
@[simp] theorem pc2569 : Artifact.submissionArtifact.instructionPC 2569 = 3878 := by rfl
@[simp] theorem pc2570 : Artifact.submissionArtifact.instructionPC 2570 = 3879 := by rfl
@[simp] theorem pc2571 : Artifact.submissionArtifact.instructionPC 2571 = 3881 := by rfl
@[simp] theorem pc2572 : Artifact.submissionArtifact.instructionPC 2572 = 3882 := by rfl
@[simp] theorem pc2573 : Artifact.submissionArtifact.instructionPC 2573 = 3883 := by rfl
@[simp] theorem pc2574 : Artifact.submissionArtifact.instructionPC 2574 = 3884 := by rfl
@[simp] theorem pc2575 : Artifact.submissionArtifact.instructionPC 2575 = 3885 := by rfl
@[simp] theorem pc2576 : Artifact.submissionArtifact.instructionPC 2576 = 3886 := by rfl
@[simp] theorem pc2577 : Artifact.submissionArtifact.instructionPC 2577 = 3887 := by rfl
@[simp] theorem pc2578 : Artifact.submissionArtifact.instructionPC 2578 = 3888 := by rfl
@[simp] theorem pc2579 : Artifact.submissionArtifact.instructionPC 2579 = 3889 := by rfl
@[simp] theorem pc2580 : Artifact.submissionArtifact.instructionPC 2580 = 3890 := by rfl
@[simp] theorem pc2581 : Artifact.submissionArtifact.instructionPC 2581 = 3893 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
