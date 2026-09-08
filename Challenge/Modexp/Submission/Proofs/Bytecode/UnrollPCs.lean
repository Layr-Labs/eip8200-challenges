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
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2255 = 3480 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2256 = 3481 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2257 = 3483 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2258 = 3484 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2259 = 3485 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2260 = 3486 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2261 = 3488 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2262 = 3489 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2263 = 3491 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2264 = 3492 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2265 = 3493 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2266 = 3494 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2267 = 3495 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2268 = 3497 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2269 = 3498 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2270 = 3499 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2271 = 3500 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2272 = 3501 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2273 = 3502 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2274 = 3503 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2275 = 3504 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2276 = 3505 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2277 = 3506 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2278 = 3508 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2279 = 3509 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2280 = 3511 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2281 = 3512 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2282 = 3513 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2283 = 3514 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2284 = 3515 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2285 = 3517 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2286 = 3518 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2287 = 3519 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2288 = 3520 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2289 = 3521 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2290 = 3522 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2291 = 3523 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2292 = 3524 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2293 = 3525 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2294 = 3526 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2295 = 3528 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2296 = 3529 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2297 = 3531 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2298 = 3532 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2299 = 3533 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2300 = 3534 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2301 = 3535 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2302 = 3537 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2303 = 3538 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2304 = 3539 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2305 = 3540 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2306 = 3541 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2307 = 3542 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2308 = 3543 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2309 = 3544 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2310 = 3545 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2311 = 3546 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2312 = 3548 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2313 = 3549 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2314 = 3551 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2315 = 3552 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2316 = 3553 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2317 = 3554 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2318 = 3555 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2319 = 3557 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2320 = 3558 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2321 = 3559 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2322 = 3560 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2323 = 3561 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2324 = 3562 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2325 = 3563 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2326 = 3564 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2327 = 3565 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2328 = 3566 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2329 = 3568 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2330 = 3569 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2331 = 3571 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2332 = 3572 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2333 = 3573 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2334 = 3574 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2335 = 3575 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2336 = 3577 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2337 = 3578 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2338 = 3579 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2339 = 3580 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2340 = 3581 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2341 = 3582 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2342 = 3583 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2343 = 3584 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2344 = 3585 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2345 = 3586 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2346 = 3588 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2347 = 3589 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2348 = 3591 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2349 = 3592 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2350 = 3593 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2351 = 3594 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2352 = 3595 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2353 = 3597 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2354 = 3598 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2355 = 3599 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2356 = 3600 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2357 = 3601 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2358 = 3602 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2359 = 3603 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2360 = 3604 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2361 = 3605 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2362 = 3606 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2363 = 3608 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2364 = 3609 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2365 = 3611 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2366 = 3612 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2367 = 3613 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2368 = 3614 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2369 = 3615 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2370 = 3617 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2371 = 3618 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2372 = 3619 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2373 = 3620 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2374 = 3621 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2375 = 3622 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2376 = 3623 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2377 = 3624 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2378 = 3625 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2379 = 3626 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2380 = 3628 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2381 = 3629 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2382 = 3631 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2383 = 3632 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2384 = 3633 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2385 = 3634 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2386 = 3635 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2387 = 3637 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2388 = 3638 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2389 = 3639 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2390 = 3640 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2391 = 3641 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2392 = 3642 := by rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2393 = 3643 := by rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2394 = 3644 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2395 = 3645 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2396 = 3646 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2397 = 3649 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
