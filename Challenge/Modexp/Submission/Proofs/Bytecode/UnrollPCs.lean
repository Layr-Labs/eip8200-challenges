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
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2266 = 3690 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2267 = 3691 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2268 = 3693 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2269 = 3694 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2270 = 3695 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2271 = 3696 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2272 = 3698 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2273 = 3699 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2274 = 3701 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2275 = 3702 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2276 = 3703 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2277 = 3704 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2278 = 3705 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2279 = 3707 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2280 = 3708 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2281 = 3709 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2282 = 3710 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2283 = 3711 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2284 = 3712 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2285 = 3713 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2286 = 3714 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2287 = 3715 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2288 = 3716 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2289 = 3718 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2290 = 3719 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2291 = 3721 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2292 = 3722 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2293 = 3723 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2294 = 3724 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2295 = 3725 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2296 = 3727 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2297 = 3728 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2298 = 3729 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2299 = 3730 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2300 = 3731 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2301 = 3732 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2302 = 3733 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2303 = 3734 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2304 = 3735 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2305 = 3736 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2306 = 3738 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2307 = 3739 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2308 = 3741 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2309 = 3742 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2310 = 3743 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2311 = 3744 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2312 = 3745 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2313 = 3747 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2314 = 3748 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2315 = 3749 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2316 = 3750 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2317 = 3751 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2318 = 3752 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2319 = 3753 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2320 = 3754 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2321 = 3755 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2322 = 3756 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2323 = 3758 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2324 = 3759 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2325 = 3761 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2326 = 3762 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2327 = 3763 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2328 = 3764 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2329 = 3765 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2330 = 3767 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2331 = 3768 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2332 = 3769 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2333 = 3770 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2334 = 3771 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2335 = 3772 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2336 = 3773 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2337 = 3774 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2338 = 3775 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2339 = 3776 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2340 = 3778 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2341 = 3779 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2342 = 3781 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2343 = 3782 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2344 = 3783 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2345 = 3784 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2346 = 3785 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2347 = 3787 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2348 = 3788 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2349 = 3789 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2350 = 3790 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2351 = 3791 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2352 = 3792 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2353 = 3793 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2354 = 3794 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2355 = 3795 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2356 = 3796 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2357 = 3798 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2358 = 3799 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2359 = 3801 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2360 = 3802 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2361 = 3803 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2362 = 3804 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2363 = 3805 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2364 = 3807 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2365 = 3808 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2366 = 3809 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2367 = 3810 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2368 = 3811 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2369 = 3812 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2370 = 3813 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2371 = 3814 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2372 = 3815 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2373 = 3816 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2374 = 3818 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2375 = 3819 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2376 = 3821 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2377 = 3822 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2378 = 3823 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2379 = 3824 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2380 = 3825 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2381 = 3827 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2382 = 3828 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2383 = 3829 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2384 = 3830 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2385 = 3831 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2386 = 3832 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2387 = 3833 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2388 = 3834 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2389 = 3835 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2390 = 3836 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2391 = 3838 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2392 = 3839 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2393 = 3841 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2394 = 3842 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2395 = 3843 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2396 = 3844 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2397 = 3845 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2398 = 3847 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2399 = 3848 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2400 = 3849 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2401 = 3850 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2402 = 3851 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2403 = 3852 := by rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2404 = 3853 := by rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2405 = 3854 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2406 = 3855 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2407 = 3856 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2408 = 3859 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
