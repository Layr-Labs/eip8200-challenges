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
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2263 = 3609 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2264 = 3610 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2265 = 3612 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2266 = 3613 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2267 = 3614 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2268 = 3615 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2269 = 3617 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2270 = 3618 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2271 = 3620 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2272 = 3621 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2273 = 3622 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2274 = 3623 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2275 = 3624 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2276 = 3626 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2277 = 3627 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2278 = 3628 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2279 = 3629 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2280 = 3630 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2281 = 3631 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2282 = 3632 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2283 = 3633 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2284 = 3634 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2285 = 3635 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2286 = 3637 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2287 = 3638 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2288 = 3640 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2289 = 3641 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2290 = 3642 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2291 = 3643 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2292 = 3644 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2293 = 3646 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2294 = 3647 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2295 = 3648 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2296 = 3649 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2297 = 3650 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2298 = 3651 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2299 = 3652 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2300 = 3653 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2301 = 3654 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2302 = 3655 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2303 = 3657 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2304 = 3658 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2305 = 3660 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2306 = 3661 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2307 = 3662 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2308 = 3663 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2309 = 3664 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2310 = 3666 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2311 = 3667 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2312 = 3668 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2313 = 3669 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2314 = 3670 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2315 = 3671 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2316 = 3672 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2317 = 3673 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2318 = 3674 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2319 = 3675 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2320 = 3677 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2321 = 3678 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2322 = 3680 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2323 = 3681 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2324 = 3682 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2325 = 3683 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2326 = 3684 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2327 = 3686 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2328 = 3687 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2329 = 3688 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2330 = 3689 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2331 = 3690 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2332 = 3691 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2333 = 3692 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2334 = 3693 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2335 = 3694 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2336 = 3695 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2337 = 3697 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2338 = 3698 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2339 = 3700 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2340 = 3701 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2341 = 3702 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2342 = 3703 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2343 = 3704 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2344 = 3706 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2345 = 3707 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2346 = 3708 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2347 = 3709 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2348 = 3710 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2349 = 3711 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2350 = 3712 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2351 = 3713 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2352 = 3714 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2353 = 3715 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2354 = 3717 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2355 = 3718 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2356 = 3720 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2357 = 3721 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2358 = 3722 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2359 = 3723 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2360 = 3724 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2361 = 3726 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2362 = 3727 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2363 = 3728 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2364 = 3729 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2365 = 3730 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2366 = 3731 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2367 = 3732 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2368 = 3733 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2369 = 3734 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2370 = 3735 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2371 = 3737 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2372 = 3738 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2373 = 3740 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2374 = 3741 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2375 = 3742 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2376 = 3743 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2377 = 3744 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2378 = 3746 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2379 = 3747 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2380 = 3748 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2381 = 3749 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2382 = 3750 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2383 = 3751 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2384 = 3752 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2385 = 3753 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2386 = 3754 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2387 = 3755 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2388 = 3757 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2389 = 3758 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2390 = 3760 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2391 = 3761 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2392 = 3762 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2393 = 3763 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2394 = 3764 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2395 = 3766 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2396 = 3767 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2397 = 3768 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2398 = 3769 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2399 = 3770 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2400 = 3771 := by rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2401 = 3772 := by rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2402 = 3773 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2403 = 3774 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2404 = 3775 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2405 = 3778 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
