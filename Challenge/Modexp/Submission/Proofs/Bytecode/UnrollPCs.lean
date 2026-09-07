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
@[simp] theorem pc2409 : Artifact.submissionArtifact.instructionPC 2409 = 3688 := by rfl
@[simp] theorem pc2410 : Artifact.submissionArtifact.instructionPC 2410 = 3689 := by rfl
@[simp] theorem pc2411 : Artifact.submissionArtifact.instructionPC 2411 = 3691 := by rfl
@[simp] theorem pc2412 : Artifact.submissionArtifact.instructionPC 2412 = 3692 := by rfl
@[simp] theorem pc2413 : Artifact.submissionArtifact.instructionPC 2413 = 3693 := by rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2414 = 3694 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2415 = 3696 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2416 = 3697 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2417 = 3699 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2418 = 3700 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2419 = 3701 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2420 = 3702 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2421 = 3703 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2422 = 3705 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2423 = 3706 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2424 = 3707 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2425 = 3708 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2426 = 3709 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2427 = 3710 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2428 = 3711 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2429 = 3712 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2430 = 3713 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2431 = 3714 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2432 = 3716 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2433 = 3717 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2434 = 3719 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2435 = 3720 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2436 = 3721 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2437 = 3722 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2438 = 3723 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2439 = 3725 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2440 = 3726 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2441 = 3727 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2442 = 3728 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2443 = 3729 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2444 = 3730 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2445 = 3731 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2446 = 3732 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2447 = 3733 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2448 = 3734 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2449 = 3736 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2450 = 3737 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2451 = 3739 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2452 = 3740 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2453 = 3741 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2454 = 3742 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2455 = 3743 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2456 = 3745 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2457 = 3746 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2458 = 3747 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2459 = 3748 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2460 = 3749 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2461 = 3750 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2462 = 3751 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2463 = 3752 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2464 = 3753 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2465 = 3754 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2466 = 3756 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2467 = 3757 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2468 = 3759 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2469 = 3760 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2470 = 3761 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2471 = 3762 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2472 = 3763 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2473 = 3765 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2474 = 3766 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2475 = 3767 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2476 = 3768 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2477 = 3769 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2478 = 3770 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2479 = 3771 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2480 = 3772 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2481 = 3773 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2482 = 3774 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2483 = 3776 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2484 = 3777 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2485 = 3779 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2486 = 3780 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2487 = 3781 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2488 = 3782 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2489 = 3783 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2490 = 3785 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2491 = 3786 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2492 = 3787 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2493 = 3788 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2494 = 3789 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2495 = 3790 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2496 = 3791 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2497 = 3792 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2498 = 3793 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2499 = 3794 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2500 = 3796 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2501 = 3797 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2502 = 3799 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2503 = 3800 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2504 = 3801 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2505 = 3802 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2506 = 3803 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2507 = 3805 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2508 = 3806 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2509 = 3807 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2510 = 3808 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2511 = 3809 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2512 = 3810 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2513 = 3811 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2514 = 3812 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2515 = 3813 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2516 = 3814 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2517 = 3816 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2518 = 3817 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2519 = 3819 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2520 = 3820 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2521 = 3821 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2522 = 3822 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2523 = 3823 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2524 = 3825 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2525 = 3826 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2526 = 3827 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2527 = 3828 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2528 = 3829 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2529 = 3830 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2530 = 3831 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2531 = 3832 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2532 = 3833 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2533 = 3834 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2534 = 3836 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2535 = 3837 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2536 = 3839 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2537 = 3840 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2538 = 3841 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2539 = 3842 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2540 = 3843 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2541 = 3845 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2542 = 3846 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2543 = 3847 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2544 = 3848 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2545 = 3849 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2546 = 3850 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2547 = 3851 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2548 = 3852 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2549 = 3853 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2550 = 3854 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2551 = 3857 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
