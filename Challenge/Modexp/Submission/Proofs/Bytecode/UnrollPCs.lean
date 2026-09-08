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

@[simp] theorem pc484 : Artifact.submissionArtifact.instructionPC 483 = 605 := by rfl
@[simp] theorem pc485 : Artifact.submissionArtifact.instructionPC 484 = 606 := by rfl
@[simp] theorem pc486 : Artifact.submissionArtifact.instructionPC 485 = 609 := by rfl
@[simp] theorem pc2414 : Artifact.submissionArtifact.instructionPC 2255 = 3177 := by rfl
@[simp] theorem pc2415 : Artifact.submissionArtifact.instructionPC 2256 = 3178 := by rfl
@[simp] theorem pc2416 : Artifact.submissionArtifact.instructionPC 2257 = 3180 := by rfl
@[simp] theorem pc2417 : Artifact.submissionArtifact.instructionPC 2258 = 3181 := by rfl
@[simp] theorem pc2418 : Artifact.submissionArtifact.instructionPC 2259 = 3182 := by rfl
@[simp] theorem pc2419 : Artifact.submissionArtifact.instructionPC 2260 = 3183 := by rfl
@[simp] theorem pc2420 : Artifact.submissionArtifact.instructionPC 2261 = 3185 := by rfl
@[simp] theorem pc2421 : Artifact.submissionArtifact.instructionPC 2262 = 3186 := by rfl
@[simp] theorem pc2422 : Artifact.submissionArtifact.instructionPC 2263 = 3188 := by rfl
@[simp] theorem pc2423 : Artifact.submissionArtifact.instructionPC 2264 = 3189 := by rfl
@[simp] theorem pc2424 : Artifact.submissionArtifact.instructionPC 2265 = 3190 := by rfl
@[simp] theorem pc2425 : Artifact.submissionArtifact.instructionPC 2266 = 3191 := by rfl
@[simp] theorem pc2426 : Artifact.submissionArtifact.instructionPC 2267 = 3192 := by rfl
@[simp] theorem pc2427 : Artifact.submissionArtifact.instructionPC 2268 = 3194 := by rfl
@[simp] theorem pc2428 : Artifact.submissionArtifact.instructionPC 2269 = 3195 := by rfl
@[simp] theorem pc2429 : Artifact.submissionArtifact.instructionPC 2270 = 3196 := by rfl
@[simp] theorem pc2430 : Artifact.submissionArtifact.instructionPC 2271 = 3197 := by rfl
@[simp] theorem pc2431 : Artifact.submissionArtifact.instructionPC 2272 = 3198 := by rfl
@[simp] theorem pc2432 : Artifact.submissionArtifact.instructionPC 2273 = 3199 := by rfl
@[simp] theorem pc2433 : Artifact.submissionArtifact.instructionPC 2274 = 3200 := by rfl
@[simp] theorem pc2434 : Artifact.submissionArtifact.instructionPC 2275 = 3201 := by rfl
@[simp] theorem pc2435 : Artifact.submissionArtifact.instructionPC 2276 = 3202 := by rfl
@[simp] theorem pc2436 : Artifact.submissionArtifact.instructionPC 2277 = 3203 := by rfl
@[simp] theorem pc2437 : Artifact.submissionArtifact.instructionPC 2278 = 3205 := by rfl
@[simp] theorem pc2438 : Artifact.submissionArtifact.instructionPC 2279 = 3206 := by rfl
@[simp] theorem pc2439 : Artifact.submissionArtifact.instructionPC 2280 = 3208 := by rfl
@[simp] theorem pc2440 : Artifact.submissionArtifact.instructionPC 2281 = 3209 := by rfl
@[simp] theorem pc2441 : Artifact.submissionArtifact.instructionPC 2282 = 3210 := by rfl
@[simp] theorem pc2442 : Artifact.submissionArtifact.instructionPC 2283 = 3211 := by rfl
@[simp] theorem pc2443 : Artifact.submissionArtifact.instructionPC 2284 = 3212 := by rfl
@[simp] theorem pc2444 : Artifact.submissionArtifact.instructionPC 2285 = 3214 := by rfl
@[simp] theorem pc2445 : Artifact.submissionArtifact.instructionPC 2286 = 3215 := by rfl
@[simp] theorem pc2446 : Artifact.submissionArtifact.instructionPC 2287 = 3216 := by rfl
@[simp] theorem pc2447 : Artifact.submissionArtifact.instructionPC 2288 = 3217 := by rfl
@[simp] theorem pc2448 : Artifact.submissionArtifact.instructionPC 2289 = 3218 := by rfl
@[simp] theorem pc2449 : Artifact.submissionArtifact.instructionPC 2290 = 3219 := by rfl
@[simp] theorem pc2450 : Artifact.submissionArtifact.instructionPC 2291 = 3220 := by rfl
@[simp] theorem pc2451 : Artifact.submissionArtifact.instructionPC 2292 = 3221 := by rfl
@[simp] theorem pc2452 : Artifact.submissionArtifact.instructionPC 2293 = 3222 := by rfl
@[simp] theorem pc2453 : Artifact.submissionArtifact.instructionPC 2294 = 3223 := by rfl
@[simp] theorem pc2454 : Artifact.submissionArtifact.instructionPC 2295 = 3225 := by rfl
@[simp] theorem pc2455 : Artifact.submissionArtifact.instructionPC 2296 = 3226 := by rfl
@[simp] theorem pc2456 : Artifact.submissionArtifact.instructionPC 2297 = 3228 := by rfl
@[simp] theorem pc2457 : Artifact.submissionArtifact.instructionPC 2298 = 3229 := by rfl
@[simp] theorem pc2458 : Artifact.submissionArtifact.instructionPC 2299 = 3230 := by rfl
@[simp] theorem pc2459 : Artifact.submissionArtifact.instructionPC 2300 = 3231 := by rfl
@[simp] theorem pc2460 : Artifact.submissionArtifact.instructionPC 2301 = 3232 := by rfl
@[simp] theorem pc2461 : Artifact.submissionArtifact.instructionPC 2302 = 3234 := by rfl
@[simp] theorem pc2462 : Artifact.submissionArtifact.instructionPC 2303 = 3235 := by rfl
@[simp] theorem pc2463 : Artifact.submissionArtifact.instructionPC 2304 = 3236 := by rfl
@[simp] theorem pc2464 : Artifact.submissionArtifact.instructionPC 2305 = 3237 := by rfl
@[simp] theorem pc2465 : Artifact.submissionArtifact.instructionPC 2306 = 3238 := by rfl
@[simp] theorem pc2466 : Artifact.submissionArtifact.instructionPC 2307 = 3239 := by rfl
@[simp] theorem pc2467 : Artifact.submissionArtifact.instructionPC 2308 = 3240 := by rfl
@[simp] theorem pc2468 : Artifact.submissionArtifact.instructionPC 2309 = 3241 := by rfl
@[simp] theorem pc2469 : Artifact.submissionArtifact.instructionPC 2310 = 3242 := by rfl
@[simp] theorem pc2470 : Artifact.submissionArtifact.instructionPC 2311 = 3243 := by rfl
@[simp] theorem pc2471 : Artifact.submissionArtifact.instructionPC 2312 = 3245 := by rfl
@[simp] theorem pc2472 : Artifact.submissionArtifact.instructionPC 2313 = 3246 := by rfl
@[simp] theorem pc2473 : Artifact.submissionArtifact.instructionPC 2314 = 3248 := by rfl
@[simp] theorem pc2474 : Artifact.submissionArtifact.instructionPC 2315 = 3249 := by rfl
@[simp] theorem pc2475 : Artifact.submissionArtifact.instructionPC 2316 = 3250 := by rfl
@[simp] theorem pc2476 : Artifact.submissionArtifact.instructionPC 2317 = 3251 := by rfl
@[simp] theorem pc2477 : Artifact.submissionArtifact.instructionPC 2318 = 3252 := by rfl
@[simp] theorem pc2478 : Artifact.submissionArtifact.instructionPC 2319 = 3254 := by rfl
@[simp] theorem pc2479 : Artifact.submissionArtifact.instructionPC 2320 = 3255 := by rfl
@[simp] theorem pc2480 : Artifact.submissionArtifact.instructionPC 2321 = 3256 := by rfl
@[simp] theorem pc2481 : Artifact.submissionArtifact.instructionPC 2322 = 3257 := by rfl
@[simp] theorem pc2482 : Artifact.submissionArtifact.instructionPC 2323 = 3258 := by rfl
@[simp] theorem pc2483 : Artifact.submissionArtifact.instructionPC 2324 = 3259 := by rfl
@[simp] theorem pc2484 : Artifact.submissionArtifact.instructionPC 2325 = 3260 := by rfl
@[simp] theorem pc2485 : Artifact.submissionArtifact.instructionPC 2326 = 3261 := by rfl
@[simp] theorem pc2486 : Artifact.submissionArtifact.instructionPC 2327 = 3262 := by rfl
@[simp] theorem pc2487 : Artifact.submissionArtifact.instructionPC 2328 = 3263 := by rfl
@[simp] theorem pc2488 : Artifact.submissionArtifact.instructionPC 2329 = 3265 := by rfl
@[simp] theorem pc2489 : Artifact.submissionArtifact.instructionPC 2330 = 3266 := by rfl
@[simp] theorem pc2490 : Artifact.submissionArtifact.instructionPC 2331 = 3268 := by rfl
@[simp] theorem pc2491 : Artifact.submissionArtifact.instructionPC 2332 = 3269 := by rfl
@[simp] theorem pc2492 : Artifact.submissionArtifact.instructionPC 2333 = 3270 := by rfl
@[simp] theorem pc2493 : Artifact.submissionArtifact.instructionPC 2334 = 3271 := by rfl
@[simp] theorem pc2494 : Artifact.submissionArtifact.instructionPC 2335 = 3272 := by rfl
@[simp] theorem pc2495 : Artifact.submissionArtifact.instructionPC 2336 = 3274 := by rfl
@[simp] theorem pc2496 : Artifact.submissionArtifact.instructionPC 2337 = 3275 := by rfl
@[simp] theorem pc2497 : Artifact.submissionArtifact.instructionPC 2338 = 3276 := by rfl
@[simp] theorem pc2498 : Artifact.submissionArtifact.instructionPC 2339 = 3277 := by rfl
@[simp] theorem pc2499 : Artifact.submissionArtifact.instructionPC 2340 = 3278 := by rfl
@[simp] theorem pc2500 : Artifact.submissionArtifact.instructionPC 2341 = 3279 := by rfl
@[simp] theorem pc2501 : Artifact.submissionArtifact.instructionPC 2342 = 3280 := by rfl
@[simp] theorem pc2502 : Artifact.submissionArtifact.instructionPC 2343 = 3281 := by rfl
@[simp] theorem pc2503 : Artifact.submissionArtifact.instructionPC 2344 = 3282 := by rfl
@[simp] theorem pc2504 : Artifact.submissionArtifact.instructionPC 2345 = 3283 := by rfl
@[simp] theorem pc2505 : Artifact.submissionArtifact.instructionPC 2346 = 3285 := by rfl
@[simp] theorem pc2506 : Artifact.submissionArtifact.instructionPC 2347 = 3286 := by rfl
@[simp] theorem pc2507 : Artifact.submissionArtifact.instructionPC 2348 = 3288 := by rfl
@[simp] theorem pc2508 : Artifact.submissionArtifact.instructionPC 2349 = 3289 := by rfl
@[simp] theorem pc2509 : Artifact.submissionArtifact.instructionPC 2350 = 3290 := by rfl
@[simp] theorem pc2510 : Artifact.submissionArtifact.instructionPC 2351 = 3291 := by rfl
@[simp] theorem pc2511 : Artifact.submissionArtifact.instructionPC 2352 = 3292 := by rfl
@[simp] theorem pc2512 : Artifact.submissionArtifact.instructionPC 2353 = 3294 := by rfl
@[simp] theorem pc2513 : Artifact.submissionArtifact.instructionPC 2354 = 3295 := by rfl
@[simp] theorem pc2514 : Artifact.submissionArtifact.instructionPC 2355 = 3296 := by rfl
@[simp] theorem pc2515 : Artifact.submissionArtifact.instructionPC 2356 = 3297 := by rfl
@[simp] theorem pc2516 : Artifact.submissionArtifact.instructionPC 2357 = 3298 := by rfl
@[simp] theorem pc2517 : Artifact.submissionArtifact.instructionPC 2358 = 3299 := by rfl
@[simp] theorem pc2518 : Artifact.submissionArtifact.instructionPC 2359 = 3300 := by rfl
@[simp] theorem pc2519 : Artifact.submissionArtifact.instructionPC 2360 = 3301 := by rfl
@[simp] theorem pc2520 : Artifact.submissionArtifact.instructionPC 2361 = 3302 := by rfl
@[simp] theorem pc2521 : Artifact.submissionArtifact.instructionPC 2362 = 3303 := by rfl
@[simp] theorem pc2522 : Artifact.submissionArtifact.instructionPC 2363 = 3305 := by rfl
@[simp] theorem pc2523 : Artifact.submissionArtifact.instructionPC 2364 = 3306 := by rfl
@[simp] theorem pc2524 : Artifact.submissionArtifact.instructionPC 2365 = 3308 := by rfl
@[simp] theorem pc2525 : Artifact.submissionArtifact.instructionPC 2366 = 3309 := by rfl
@[simp] theorem pc2526 : Artifact.submissionArtifact.instructionPC 2367 = 3310 := by rfl
@[simp] theorem pc2527 : Artifact.submissionArtifact.instructionPC 2368 = 3311 := by rfl
@[simp] theorem pc2528 : Artifact.submissionArtifact.instructionPC 2369 = 3312 := by rfl
@[simp] theorem pc2529 : Artifact.submissionArtifact.instructionPC 2370 = 3314 := by rfl
@[simp] theorem pc2530 : Artifact.submissionArtifact.instructionPC 2371 = 3315 := by rfl
@[simp] theorem pc2531 : Artifact.submissionArtifact.instructionPC 2372 = 3316 := by rfl
@[simp] theorem pc2532 : Artifact.submissionArtifact.instructionPC 2373 = 3317 := by rfl
@[simp] theorem pc2533 : Artifact.submissionArtifact.instructionPC 2374 = 3318 := by rfl
@[simp] theorem pc2534 : Artifact.submissionArtifact.instructionPC 2375 = 3319 := by rfl
@[simp] theorem pc2535 : Artifact.submissionArtifact.instructionPC 2376 = 3320 := by rfl
@[simp] theorem pc2536 : Artifact.submissionArtifact.instructionPC 2377 = 3321 := by rfl
@[simp] theorem pc2537 : Artifact.submissionArtifact.instructionPC 2378 = 3322 := by rfl
@[simp] theorem pc2538 : Artifact.submissionArtifact.instructionPC 2379 = 3323 := by rfl
@[simp] theorem pc2539 : Artifact.submissionArtifact.instructionPC 2380 = 3325 := by rfl
@[simp] theorem pc2540 : Artifact.submissionArtifact.instructionPC 2381 = 3326 := by rfl
@[simp] theorem pc2541 : Artifact.submissionArtifact.instructionPC 2382 = 3328 := by rfl
@[simp] theorem pc2542 : Artifact.submissionArtifact.instructionPC 2383 = 3329 := by rfl
@[simp] theorem pc2543 : Artifact.submissionArtifact.instructionPC 2384 = 3330 := by rfl
@[simp] theorem pc2544 : Artifact.submissionArtifact.instructionPC 2385 = 3331 := by rfl
@[simp] theorem pc2545 : Artifact.submissionArtifact.instructionPC 2386 = 3332 := by rfl
@[simp] theorem pc2546 : Artifact.submissionArtifact.instructionPC 2387 = 3334 := by rfl
@[simp] theorem pc2547 : Artifact.submissionArtifact.instructionPC 2388 = 3335 := by rfl
@[simp] theorem pc2548 : Artifact.submissionArtifact.instructionPC 2389 = 3336 := by rfl
@[simp] theorem pc2549 : Artifact.submissionArtifact.instructionPC 2390 = 3337 := by rfl
@[simp] theorem pc2550 : Artifact.submissionArtifact.instructionPC 2391 = 3338 := by rfl
@[simp] theorem pc2551 : Artifact.submissionArtifact.instructionPC 2392 = 3339 := by rfl
@[simp] theorem pc2552 : Artifact.submissionArtifact.instructionPC 2393 = 3340 := by rfl
@[simp] theorem pc2553 : Artifact.submissionArtifact.instructionPC 2394 = 3341 := by rfl
@[simp] theorem pc2554 : Artifact.submissionArtifact.instructionPC 2395 = 3342 := by rfl
@[simp] theorem pc2555 : Artifact.submissionArtifact.instructionPC 2396 = 3343 := by rfl
@[simp] theorem pc2556 : Artifact.submissionArtifact.instructionPC 2397 = 3346 := by rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.UnrollPCs
