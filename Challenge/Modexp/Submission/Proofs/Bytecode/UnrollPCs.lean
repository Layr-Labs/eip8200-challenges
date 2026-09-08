import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
/-!
# Program counters for the unrolled exponent-bit block

The block holds eight byte-identical copies of the bit body.  Copy `k` starts
at instruction index `2365 + 17 * k` and at byte `3119 + 20 * k`; the entry
`JUMPDEST`, the `base - 1` it derives and the closing jump sit on either side
of the eight copies.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem pc484 : Artifact.submissionArtifact.instructionPC 484 = 606 := by rfl
@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 485 = 607 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 486 = 610 := by rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2260 = 3198 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2261 = 3199 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2262 = 3201 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2263 = 3202 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2264 = 3203 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2265 = 3204 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2266 = 3206 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2267 = 3207 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2268 = 3209 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2269 = 3210 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2270 = 3211 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2271 = 3212 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2272 = 3213 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2273 = 3215 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2274 = 3216 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2275 = 3217 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2276 = 3218 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2277 = 3219 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2278 = 3220 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2279 = 3221 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2280 = 3222 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2281 = 3223 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2282 = 3224 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2283 = 3226 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2284 = 3227 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2285 = 3229 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2286 = 3230 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2287 = 3231 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2288 = 3232 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2289 = 3233 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2290 = 3235 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2291 = 3236 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2292 = 3237 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2293 = 3238 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2294 = 3239 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2295 = 3240 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2296 = 3241 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2297 = 3242 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2298 = 3243 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2299 = 3244 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2300 = 3246 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2301 = 3247 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2302 = 3249 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2303 = 3250 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2304 = 3251 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2305 = 3252 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2306 = 3253 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2307 = 3255 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2308 = 3256 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2309 = 3257 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2310 = 3258 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2311 = 3259 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2312 = 3260 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2313 = 3261 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2314 = 3262 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2315 = 3263 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2316 = 3264 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2317 = 3266 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2318 = 3267 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2319 = 3269 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2320 = 3270 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2321 = 3271 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2322 = 3272 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2323 = 3273 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2324 = 3275 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2325 = 3276 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2326 = 3277 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2327 = 3278 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2328 = 3279 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2329 = 3280 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2330 = 3281 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2331 = 3282 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2332 = 3283 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2333 = 3284 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2334 = 3286 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2335 = 3287 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2336 = 3289 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2337 = 3290 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2338 = 3291 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2339 = 3292 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2340 = 3293 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2341 = 3295 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2342 = 3296 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2343 = 3297 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2344 = 3298 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2345 = 3299 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2346 = 3300 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2347 = 3301 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2348 = 3302 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2349 = 3303 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2350 = 3304 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2351 = 3306 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2352 = 3307 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2353 = 3309 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2354 = 3310 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2355 = 3311 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2356 = 3312 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2357 = 3313 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2358 = 3315 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2359 = 3316 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2360 = 3317 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2361 = 3318 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2362 = 3319 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2363 = 3320 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2364 = 3321 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2365 = 3322 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2366 = 3323 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2367 = 3324 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2368 = 3326 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2369 = 3327 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2370 = 3329 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2371 = 3330 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2372 = 3331 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2373 = 3332 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2374 = 3333 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2375 = 3335 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2376 = 3336 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2377 = 3337 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2378 = 3338 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2379 = 3339 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2380 = 3340 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2381 = 3341 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2382 = 3342 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2383 = 3343 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2384 = 3344 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2385 = 3346 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2386 = 3347 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2387 = 3349 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2388 = 3350 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2389 = 3351 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2390 = 3352 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2391 = 3353 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2392 = 3355 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2393 = 3356 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2394 = 3357 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2395 = 3358 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2396 = 3359 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2397 = 3360 := by rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2398 = 3361 := by rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2399 = 3362 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2400 = 3363 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2401 = 3364 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2402 = 3367 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
