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
@[simp] theorem pc2361 : Artifact.submissionArtifact.instructionPC 2361 = 3606 := by rfl
@[simp] theorem pc2362 : Artifact.submissionArtifact.instructionPC 2362 = 3607 := by rfl
@[simp] theorem pc2363 : Artifact.submissionArtifact.instructionPC 2363 = 3609 := by rfl
@[simp] theorem pc2364 : Artifact.submissionArtifact.instructionPC 2364 = 3610 := by rfl
@[simp] theorem pc2365 : Artifact.submissionArtifact.instructionPC 2365 = 3611 := by rfl
@[simp] theorem pc2366 : Artifact.submissionArtifact.instructionPC 2366 = 3612 := by rfl
@[simp] theorem pc2367 : Artifact.submissionArtifact.instructionPC 2367 = 3614 := by rfl
@[simp] theorem pc2368 : Artifact.submissionArtifact.instructionPC 2368 = 3615 := by rfl
@[simp] theorem pc2369 : Artifact.submissionArtifact.instructionPC 2369 = 3617 := by rfl
@[simp] theorem pc2370 : Artifact.submissionArtifact.instructionPC 2370 = 3618 := by rfl
@[simp] theorem pc2371 : Artifact.submissionArtifact.instructionPC 2371 = 3619 := by rfl
@[simp] theorem pc2372 : Artifact.submissionArtifact.instructionPC 2372 = 3620 := by rfl
@[simp] theorem pc2373 : Artifact.submissionArtifact.instructionPC 2373 = 3621 := by rfl
@[simp] theorem pc2374 : Artifact.submissionArtifact.instructionPC 2374 = 3623 := by rfl
@[simp] theorem pc2375 : Artifact.submissionArtifact.instructionPC 2375 = 3624 := by rfl
@[simp] theorem pc2376 : Artifact.submissionArtifact.instructionPC 2376 = 3625 := by rfl
@[simp] theorem pc2377 : Artifact.submissionArtifact.instructionPC 2377 = 3626 := by rfl
@[simp] theorem pc2378 : Artifact.submissionArtifact.instructionPC 2378 = 3627 := by rfl
@[simp] theorem pc2379 : Artifact.submissionArtifact.instructionPC 2379 = 3628 := by rfl
@[simp] theorem pc2380 : Artifact.submissionArtifact.instructionPC 2380 = 3629 := by rfl
@[simp] theorem pc2381 : Artifact.submissionArtifact.instructionPC 2381 = 3630 := by rfl
@[simp] theorem pc2382 : Artifact.submissionArtifact.instructionPC 2382 = 3631 := by rfl
@[simp] theorem pc2383 : Artifact.submissionArtifact.instructionPC 2383 = 3632 := by rfl
@[simp] theorem pc2384 : Artifact.submissionArtifact.instructionPC 2384 = 3634 := by rfl
@[simp] theorem pc2385 : Artifact.submissionArtifact.instructionPC 2385 = 3635 := by rfl
@[simp] theorem pc2386 : Artifact.submissionArtifact.instructionPC 2386 = 3637 := by rfl
@[simp] theorem pc2387 : Artifact.submissionArtifact.instructionPC 2387 = 3638 := by rfl
@[simp] theorem pc2388 : Artifact.submissionArtifact.instructionPC 2388 = 3639 := by rfl
@[simp] theorem pc2389 : Artifact.submissionArtifact.instructionPC 2389 = 3640 := by rfl
@[simp] theorem pc2390 : Artifact.submissionArtifact.instructionPC 2390 = 3641 := by rfl
@[simp] theorem pc2391 : Artifact.submissionArtifact.instructionPC 2391 = 3643 := by rfl
@[simp] theorem pc2392 : Artifact.submissionArtifact.instructionPC 2392 = 3644 := by rfl
@[simp] theorem pc2393 : Artifact.submissionArtifact.instructionPC 2393 = 3645 := by rfl
@[simp] theorem pc2394 : Artifact.submissionArtifact.instructionPC 2394 = 3646 := by rfl
@[simp] theorem pc2395 : Artifact.submissionArtifact.instructionPC 2395 = 3647 := by rfl
@[simp] theorem pc2396 : Artifact.submissionArtifact.instructionPC 2396 = 3648 := by rfl
@[simp] theorem pc2397 : Artifact.submissionArtifact.instructionPC 2397 = 3649 := by rfl
@[simp] theorem pc2398 : Artifact.submissionArtifact.instructionPC 2398 = 3650 := by rfl
@[simp] theorem pc2399 : Artifact.submissionArtifact.instructionPC 2399 = 3651 := by rfl
@[simp] theorem pc2400 : Artifact.submissionArtifact.instructionPC 2400 = 3652 := by rfl
@[simp] theorem pc2401 : Artifact.submissionArtifact.instructionPC 2401 = 3654 := by rfl
@[simp] theorem pc2402 : Artifact.submissionArtifact.instructionPC 2402 = 3655 := by rfl
@[simp] theorem pc2403 : Artifact.submissionArtifact.instructionPC 2403 = 3657 := by rfl
@[simp] theorem pc2404 : Artifact.submissionArtifact.instructionPC 2404 = 3658 := by rfl
@[simp] theorem pc2405 : Artifact.submissionArtifact.instructionPC 2405 = 3659 := by rfl
@[simp] theorem pc2406 : Artifact.submissionArtifact.instructionPC 2406 = 3660 := by rfl
@[simp] theorem pc2407 : Artifact.submissionArtifact.instructionPC 2407 = 3661 := by rfl
@[simp] theorem pc2408 : Artifact.submissionArtifact.instructionPC 2408 = 3663 := by rfl
@[simp] theorem pc2409 : Artifact.submissionArtifact.instructionPC 2409 = 3664 := by rfl
@[simp] theorem pc2410 : Artifact.submissionArtifact.instructionPC 2410 = 3665 := by rfl
@[simp] theorem pc2411 : Artifact.submissionArtifact.instructionPC 2411 = 3666 := by rfl
@[simp] theorem pc2412 : Artifact.submissionArtifact.instructionPC 2412 = 3667 := by rfl
@[simp] theorem pc2413 : Artifact.submissionArtifact.instructionPC 2413 = 3668 := by rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2414 = 3669 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2415 = 3670 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2416 = 3671 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2417 = 3672 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2418 = 3674 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2419 = 3675 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2420 = 3677 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2421 = 3678 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2422 = 3679 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2423 = 3680 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2424 = 3681 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2425 = 3683 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2426 = 3684 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2427 = 3685 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2428 = 3686 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2429 = 3687 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2430 = 3688 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2431 = 3689 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2432 = 3690 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2433 = 3691 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2434 = 3692 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2435 = 3694 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2436 = 3695 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2437 = 3697 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2438 = 3698 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2439 = 3699 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2440 = 3700 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2441 = 3701 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2442 = 3703 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2443 = 3704 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2444 = 3705 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2445 = 3706 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2446 = 3707 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2447 = 3708 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2448 = 3709 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2449 = 3710 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2450 = 3711 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2451 = 3712 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2452 = 3714 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2453 = 3715 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2454 = 3717 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2455 = 3718 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2456 = 3719 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2457 = 3720 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2458 = 3721 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2459 = 3723 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2460 = 3724 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2461 = 3725 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2462 = 3726 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2463 = 3727 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2464 = 3728 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2465 = 3729 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2466 = 3730 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2467 = 3731 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2468 = 3732 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2469 = 3734 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2470 = 3735 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2471 = 3737 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2472 = 3738 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2473 = 3739 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2474 = 3740 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2475 = 3741 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2476 = 3743 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2477 = 3744 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2478 = 3745 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2479 = 3746 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2480 = 3747 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2481 = 3748 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2482 = 3749 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2483 = 3750 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2484 = 3751 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2485 = 3752 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2486 = 3754 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2487 = 3755 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2488 = 3757 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2489 = 3758 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2490 = 3759 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2491 = 3760 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2492 = 3761 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2493 = 3763 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2494 = 3764 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2495 = 3765 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2496 = 3766 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2497 = 3767 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2498 = 3768 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2499 = 3769 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2500 = 3770 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2501 = 3771 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2502 = 3772 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2503 = 3775 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
