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
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2316 = 3613 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2317 = 3614 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2318 = 3616 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2319 = 3617 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2320 = 3618 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2321 = 3619 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2322 = 3621 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2323 = 3622 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2324 = 3624 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2325 = 3625 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2326 = 3626 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2327 = 3627 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2328 = 3628 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2329 = 3630 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2330 = 3631 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2331 = 3632 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2332 = 3633 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2333 = 3634 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2334 = 3635 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2335 = 3636 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2336 = 3637 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2337 = 3638 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2338 = 3639 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2339 = 3641 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2340 = 3642 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2341 = 3644 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2342 = 3645 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2343 = 3646 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2344 = 3647 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2345 = 3648 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2346 = 3650 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2347 = 3651 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2348 = 3652 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2349 = 3653 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2350 = 3654 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2351 = 3655 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2352 = 3656 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2353 = 3657 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2354 = 3658 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2355 = 3659 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2356 = 3661 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2357 = 3662 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2358 = 3664 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2359 = 3665 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2360 = 3666 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2361 = 3667 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2362 = 3668 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2363 = 3670 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2364 = 3671 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2365 = 3672 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2366 = 3673 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2367 = 3674 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2368 = 3675 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2369 = 3676 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2370 = 3677 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2371 = 3678 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2372 = 3679 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2373 = 3681 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2374 = 3682 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2375 = 3684 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2376 = 3685 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2377 = 3686 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2378 = 3687 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2379 = 3688 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2380 = 3690 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2381 = 3691 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2382 = 3692 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2383 = 3693 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2384 = 3694 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2385 = 3695 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2386 = 3696 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2387 = 3697 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2388 = 3698 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2389 = 3699 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2390 = 3701 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2391 = 3702 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2392 = 3704 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2393 = 3705 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2394 = 3706 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2395 = 3707 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2396 = 3708 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2397 = 3710 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2398 = 3711 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2399 = 3712 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2400 = 3713 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2401 = 3714 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2402 = 3715 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2403 = 3716 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2404 = 3717 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2405 = 3718 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2406 = 3719 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2407 = 3721 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2408 = 3722 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2409 = 3724 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2410 = 3725 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2411 = 3726 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2412 = 3727 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2413 = 3728 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2414 = 3730 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2415 = 3731 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2416 = 3732 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2417 = 3733 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2418 = 3734 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2419 = 3735 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2420 = 3736 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2421 = 3737 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2422 = 3738 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2423 = 3739 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2424 = 3741 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2425 = 3742 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2426 = 3744 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2427 = 3745 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2428 = 3746 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2429 = 3747 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2430 = 3748 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2431 = 3750 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2432 = 3751 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2433 = 3752 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2434 = 3753 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2435 = 3754 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2436 = 3755 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2437 = 3756 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2438 = 3757 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2439 = 3758 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2440 = 3759 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2441 = 3761 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2442 = 3762 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2443 = 3764 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2444 = 3765 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2445 = 3766 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2446 = 3767 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2447 = 3768 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2448 = 3770 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2449 = 3771 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2450 = 3772 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2451 = 3773 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2452 = 3774 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2453 = 3775 := by rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2454 = 3776 := by rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2455 = 3777 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2456 = 3778 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2457 = 3779 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2458 = 3782 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
