import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The block holds eight byte-identical copies of the bit body.  Copy `k` starts
at instruction index `2365 + 17 * k` and at byte `3375 + 20 * k`; the entry
`JUMPDEST`, the `base - 1` it derives and the closing jump sit on either side
of the eight copies.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem pc484 : Artifact.submissionArtifact.instructionPC 482 = 604 := by rfl
@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 483 = 605 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 484 = 608 := by rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2472 = 3421 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2473 = 3422 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2474 = 3424 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2475 = 3425 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2476 = 3426 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2477 = 3427 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2478 = 3429 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2479 = 3430 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2480 = 3432 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2481 = 3433 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2482 = 3434 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2483 = 3435 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2484 = 3436 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2485 = 3438 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2486 = 3439 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2487 = 3440 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2488 = 3441 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2489 = 3442 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2490 = 3443 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2491 = 3444 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2492 = 3445 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2493 = 3446 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2494 = 3447 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2495 = 3449 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2496 = 3450 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2497 = 3452 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2498 = 3453 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2499 = 3454 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2500 = 3455 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2501 = 3456 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2502 = 3458 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2503 = 3459 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2504 = 3460 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2505 = 3461 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2506 = 3462 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2507 = 3463 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2508 = 3464 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2509 = 3465 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2510 = 3466 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2511 = 3467 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2512 = 3469 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2513 = 3470 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2514 = 3472 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2515 = 3473 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2516 = 3474 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2517 = 3475 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2518 = 3476 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2519 = 3478 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2520 = 3479 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2521 = 3480 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2522 = 3481 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2523 = 3482 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2524 = 3483 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2525 = 3484 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2526 = 3485 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2527 = 3486 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2528 = 3487 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2529 = 3489 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2530 = 3490 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2531 = 3492 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2532 = 3493 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2533 = 3494 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2534 = 3495 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2535 = 3496 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2536 = 3498 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2537 = 3499 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2538 = 3500 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2539 = 3501 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2540 = 3502 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2541 = 3503 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2542 = 3504 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2543 = 3505 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2544 = 3506 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2545 = 3507 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2546 = 3509 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2547 = 3510 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2548 = 3512 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2549 = 3513 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2550 = 3514 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2551 = 3515 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2552 = 3516 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2553 = 3518 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2554 = 3519 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2555 = 3520 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2556 = 3521 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2557 = 3522 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2558 = 3523 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2559 = 3524 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2560 = 3525 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2561 = 3526 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2562 = 3527 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2563 = 3529 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2564 = 3530 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2565 = 3532 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2566 = 3533 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2567 = 3534 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2568 = 3535 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2569 = 3536 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2570 = 3538 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2571 = 3539 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2572 = 3540 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2573 = 3541 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2574 = 3542 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2575 = 3543 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2576 = 3544 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2577 = 3545 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2578 = 3546 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2579 = 3547 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2580 = 3549 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2581 = 3550 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2582 = 3552 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2583 = 3553 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2584 = 3554 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2585 = 3555 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2586 = 3556 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2587 = 3558 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2588 = 3559 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2589 = 3560 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2590 = 3561 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2591 = 3562 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2592 = 3563 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2593 = 3564 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2594 = 3565 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2595 = 3566 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2596 = 3567 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2597 = 3569 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2598 = 3570 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2599 = 3572 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2600 = 3573 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2601 = 3574 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2602 = 3575 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2603 = 3576 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2604 = 3578 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2605 = 3579 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2606 = 3580 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2607 = 3581 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2608 = 3582 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2609 = 3583 := by rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2610 = 3584 := by rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2611 = 3585 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2612 = 3586 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2613 = 3587 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2614 = 3590 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
