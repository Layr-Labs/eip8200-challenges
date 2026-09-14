import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block of the selected shift-reduce program. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2089 .JUMPDEST,
   opAt 2090 (.Dup ⟨0, by decide⟩),
   opAt 2091 (.Dup ⟨3, by decide⟩),
   opAt 2092 .EQ,
   pushAt 2093 0 0,
   opAt 2094 .MLOAD,
   pushAt 2095 1 255,
   opAt 2096 .SHR,
   opAt 2097 .AND,
   opAt 2098 .ISZERO,
   pushAt 2099 2 2831,
   opAt 2100 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2101 (.Dup ⟨0, by decide⟩),
   pushAt 2102 1 96,
   pushAt 2103 2 2112,
   opAt 2104 .CALLDATACOPY,
   pushAt 2105 0 0,
   pushAt 2106 2 2080,
   opAt 2107 .MSTORE,
   pushAt 2108 2 2848,
   pushAt 2109 2 512,
   pushAt 2110 2 4330,
   opAt 2111 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2112 .JUMPDEST,
   pushAt 2113 1 1,
   pushAt 2114 2 1024,
   opAt 2115 .MSTORE,
   pushAt 2116 2 881,
   pushAt 2117 2 1024,
   pushAt 2118 2 1658,
   opAt 2119 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2125 1 1, pushAt 2126 2 2752, opAt 2127 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2149 .POP,
   opAt 2150 .POP,
   pushAt 2151 0 0,
   opAt 2152 .MLOAD,
   opAt 2153 (.Dup ⟨0, by decide⟩),
   pushAt 2154 0 0,
   opAt 2155 .SUB,
   opAt 2156 (.Dup ⟨1, by decide⟩),
   opAt 2157 .AND,
   opAt 2158 (.Dup ⟨0, by decide⟩),
   pushAt 2159 2 1536,
   opAt 2160 .MSTORE,
   opAt 2161 (.Dup ⟨0, by decide⟩),
   opAt 2162 (.Dup ⟨2, by decide⟩),
   opAt 2163 .DIV,
   opAt 2164 (.Dup ⟨0, by decide⟩),
   pushAt 2165 2 1568,
   opAt 2166 .MSTORE,
   opAt 2167 (.Dup ⟨1, by decide⟩),
   opAt 2168 (.Dup ⟨0, by decide⟩),
   pushAt 2169 0 0,
   opAt 2170 .SUB,
   opAt 2171 .DIV,
   pushAt 2172 1 1,
   opAt 2173 .ADD,
   pushAt 2174 2 1600,
   opAt 2175 .MSTORE,
   opAt 2176 (.Dup ⟨0, by decide⟩),
   opAt 2177 (.Dup ⟨0, by decide⟩),
   pushAt 2178 0 0,
   opAt 2179 .SUB,
   opAt 2180 .MOD,
   pushAt 2181 2 1632,
   opAt 2182 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2183 (.Dup ⟨0, by decide⟩),
   pushAt 2184 1 3,
   opAt 2185 .MUL,
   pushAt 2186 1 2,
   opAt 2187 .XOR,
   opAt 2188 (.Dup ⟨0, by decide⟩),
   opAt 2189 (.Dup ⟨2, by decide⟩),
   opAt 2190 .MUL,
   pushAt 2191 1 2,
   opAt 2192 .SUB,
   opAt 2193 .MUL,
   opAt 2194 (.Dup ⟨0, by decide⟩),
   opAt 2195 (.Dup ⟨2, by decide⟩),
   opAt 2196 .MUL,
   pushAt 2197 1 2,
   opAt 2198 .SUB,
   opAt 2199 .MUL,
   opAt 2200 (.Dup ⟨0, by decide⟩),
   opAt 2201 (.Dup ⟨2, by decide⟩),
   opAt 2202 .MUL,
   pushAt 2203 1 2,
   opAt 2204 .SUB,
   opAt 2205 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2206 (.Dup ⟨0, by decide⟩),
   opAt 2207 (.Dup ⟨2, by decide⟩),
   opAt 2208 .MUL,
   pushAt 2209 1 2,
   opAt 2210 .SUB,
   opAt 2211 .MUL,
   opAt 2212 (.Dup ⟨0, by decide⟩),
   opAt 2213 (.Dup ⟨2, by decide⟩),
   opAt 2214 .MUL,
   pushAt 2215 1 2,
   opAt 2216 .SUB,
   opAt 2217 .MUL,
   opAt 2218 (.Dup ⟨0, by decide⟩),
   opAt 2219 (.Dup ⟨2, by decide⟩),
   opAt 2220 .MUL,
   pushAt 2221 1 2,
   opAt 2222 .SUB,
   opAt 2223 .MUL,
   pushAt 2224 2 1664,
   opAt 2225 .MSTORE,
   opAt 2226 .POP,
   opAt 2227 .POP,
   opAt 2228 .POP,
   opAt 2229 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2261 .JUMPDEST,
   opAt 2262 (.Dup ⟨0, by decide⟩),
   opAt 2263 .ISZERO,
   pushAt 2264 2 3502,
   opAt 2265 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2266 (.Dup ⟨1, by decide⟩),
   pushAt 2267 2 512,
   pushAt 2268 2 2080,
   opAt 2269 .MCOPY,
   pushAt 2270 0 0,
   pushAt 2271 2 2784,
   opAt 2272 .MLOAD,
   opAt 2273 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2274 2 512,
   opAt 2275 .MLOAD,
   pushAt 2276 2 1536,
   opAt 2277 .MLOAD,
   opAt 2278 (.Dup ⟨1, by decide⟩),
   opAt 2279 .DIV,
   opAt 2280 (.Swap ⟨0, by decide⟩),
   pushAt 2281 2 1600,
   opAt 2282 .MLOAD,
   opAt 2283 .MUL,
   pushAt 2284 2 1536,
   opAt 2285 .MLOAD,
   pushAt 2286 2 544,
   opAt 2287 .MLOAD,
   opAt 2288 .DIV,
   opAt 2289 .ADD,
   pushAt 2290 2 1568,
   opAt 2291 .MLOAD,
   opAt 2292 (.Dup ⟨0, by decide⟩),
   pushAt 2293 2 1632,
   opAt 2294 .MLOAD,
   opAt 2295 (.Dup ⟨4, by decide⟩),
   opAt 2296 .MULMOD,
   opAt 2297 (.Dup ⟨2, by decide⟩),
   opAt 2298 .ADDMOD,
   opAt 2299 (.Swap ⟨0, by decide⟩),
   opAt 2300 .SUB,
   pushAt 2301 2 1664,
   opAt 2302 .MLOAD,
   opAt 2303 .MUL,
   opAt 2304 (.Dup ⟨0, by decide⟩),
   pushAt 2305 0 0,
   opAt 2306 .MLOAD,
   opAt 2307 .MUL,
   pushAt 2308 2 544,
   opAt 2309 .MLOAD,
   opAt 2310 .SUB,
   pushAt 2311 1 32,
   opAt 2312 .MLOAD,
   pushAt 2313 1 128,
   opAt 2314 .SHR,
   opAt 2315 (.Dup ⟨2, by decide⟩),
   pushAt 2316 1 128,
   opAt 2317 .SHR,
   opAt 2318 .MUL,
   opAt 2319 .GT,
   opAt 2320 (.Swap ⟨0, by decide⟩),
   opAt 2321 .SUB,
   opAt 2322 (.Swap ⟨0, by decide⟩),
   pushAt 2323 2 1568,
   opAt 2324 .MLOAD,
   opAt 2325 .GT,
   opAt 2326 .ISZERO,
   pushAt 2327 0 0,
   opAt 2328 .SUB,
   opAt 2329 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2330 0 0,
   pushAt 2331 1 31,
   opAt 2332 .NOT,
   pushAt 2333 0 0,
   opAt 2334 .NOT,
   pushAt 2335 2 2784,
   opAt 2336 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2342 .JUMPDEST,
   pushAt 2343 2 832,
   opAt 2344 (.Dup ⟨1, by decide⟩),
   opAt 2345 .SUB,
   opAt 2346 .MLOAD,
   opAt 2347 (.Dup ⟨2, by decide⟩),
   opAt 2348 (.Dup ⟨6, by decide⟩),
   opAt 2349 (.Dup ⟨2, by decide⟩),
   opAt 2350 .MUL,
   opAt 2351 (.Swap ⟨1, by decide⟩),
   opAt 2352 (.Dup ⟨7, by decide⟩),
   opAt 2353 .MULMOD,
   opAt 2354 (.Dup ⟨1, by decide⟩),
   opAt 2355 (.Dup ⟨1, by decide⟩),
   opAt 2356 .LT,
   opAt 2357 .SUB,
   opAt 2358 (.Dup ⟨5, by decide⟩),
   opAt 2359 (.Dup ⟨2, by decide⟩),
   opAt 2360 .ADD,
   opAt 2361 (.Dup ⟨0, by decide⟩),
   opAt 2362 (.Swap ⟨6, by decide⟩),
   opAt 2363 .GT,
   opAt 2364 .SUB,
   opAt 2365 .SUB,
   opAt 2366 (.Dup ⟨4, by decide⟩),
   opAt 2367 (.Dup ⟨2, by decide⟩),
   opAt 2368 .MLOAD,
   opAt 2369 .ADD,
   opAt 2370 (.Dup ⟨0, by decide⟩),
   opAt 2371 (.Swap ⟨5, by decide⟩),
   opAt 2372 .GT,
   opAt 2373 .ADD,
   opAt 2374 (.Swap ⟨3, by decide⟩),
   opAt 2375 (.Dup ⟨1, by decide⟩),
   opAt 2376 .MSTORE,
   opAt 2377 (.Dup ⟨2, by decide⟩),
   opAt 2378 .ADD,
   pushAt 2490 2 2080,
   opAt 2491 (.Dup ⟨1, by decide⟩),
   opAt 2492 .GT,
   pushAt 2493 2 3150,
   opAt 2494 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2495 .POP,
   opAt 2496 .POP,
   opAt 2497 .POP,
   pushAt 2498 2 2080,
   opAt 2499 .MLOAD,
   opAt 2500 (.Dup ⟨1, by decide⟩),
   opAt 2501 .ADD,
   opAt 2502 (.Dup ⟨0, by decide⟩),
   opAt 2503 (.Swap ⟨1, by decide⟩),
   opAt 2504 .GT,
   opAt 2505 (.Dup ⟨1, by decide⟩),
   opAt 2506 (.Dup ⟨3, by decide⟩),
   opAt 2507 .GT,
   opAt 2508 .GT,
   opAt 2509 (.Swap ⟨1, by decide⟩),
   opAt 2510 (.Swap ⟨0, by decide⟩),
   opAt 2511 .SUB,
   opAt 2512 (.Dup ⟨0, by decide⟩),
   pushAt 2513 2 2080,
   opAt 2514 .MSTORE,
   opAt 2515 (.Dup ⟨1, by decide⟩),
   opAt 2516 .OR,
   pushAt 2517 2 3358,
   opAt 2518 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2526 .JUMPDEST,
   opAt 2527 .ISZERO,
   pushAt 2528 2 3443,
   opAt 2529 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2530 .JUMPDEST,
   pushAt 2531 0 0,
   pushAt 2532 2 2784,
   opAt 2533 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2534 .JUMPDEST,
   opAt 2535 (.Dup ⟨0, by decide⟩),
   opAt 2536 .MLOAD,
   pushAt 2537 2 2112,
   opAt 2538 (.Dup ⟨2, by decide⟩),
   opAt 2539 .JUMPDEST,
   opAt 2540 .SUB,
   opAt 2541 .MLOAD,
   opAt 2542 (.Dup ⟨1, by decide⟩),
   opAt 2543 .ADD,
   opAt 2544 (.Dup ⟨0, by decide⟩),
   opAt 2545 (.Dup ⟨2, by decide⟩),
   opAt 2546 .GT,
   opAt 2547 (.Swap ⟨1, by decide⟩),
   opAt 2548 .POP,
   opAt 2549 (.Dup ⟨3, by decide⟩),
   opAt 2550 .ADD,
   opAt 2551 (.Dup ⟨0, by decide⟩),
   opAt 2552 (.Dup ⟨4, by decide⟩),
   opAt 2553 .GT,
   opAt 2554 (.Swap ⟨3, by decide⟩),
   opAt 2555 .POP,
   opAt 2556 (.Dup ⟨2, by decide⟩),
   opAt 2557 .MSTORE,
   opAt 2558 (.Swap ⟨0, by decide⟩),
   opAt 2559 (.Swap ⟨1, by decide⟩),
   opAt 2560 .OR,
   opAt 2561 (.Swap ⟨0, by decide⟩),
   pushAt 2562 1 31,
   opAt 2563 .NOT,
   opAt 2564 .ADD,
   pushAt 2565 2 2111,
   opAt 2566 (.Dup ⟨1, by decide⟩),
   opAt 2567 .GT,
   pushAt 2568 2 3370,
   opAt 2569 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2570 .POP,
   pushAt 2571 2 2080,
   opAt 2572 .MLOAD,
   opAt 2573 (.Dup ⟨1, by decide⟩),
   opAt 2574 .ADD,
   opAt 2575 (.Dup ⟨0, by decide⟩),
   pushAt 2576 2 2080,
   opAt 2577 .MSTORE,
   opAt 2578 .LT,
   opAt 2579 .ISZERO,
   pushAt 2580 2 3364,
   opAt 2581 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   pushAt 2583 2 2080,
   opAt 2584 .MLOAD,
   opAt 2585 (.Dup ⟨0, by decide⟩),
   opAt 2586 .ISZERO,
   pushAt 2587 2 3345,
   opAt 2588 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   pushAt 2583 2 2080,
   opAt 2584 .MLOAD,
   opAt 2585 (.Dup ⟨0, by decide⟩),
   opAt 2586 .ISZERO,
   pushAt 2587 2 3345,
   opAt 2588 .JUMPI,
   opAt 2589 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2590 .JUMPDEST,
   pushAt 2591 0 0,
   pushAt 2592 2 2784,
   opAt 2593 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2594 .JUMPDEST,
   opAt 2595 (.Dup ⟨0, by decide⟩),
   opAt 2596 .MLOAD,
   pushAt 2597 2 2112,
   opAt 2598 (.Dup ⟨2, by decide⟩),
   opAt 2599 .SUB,
   opAt 2600 .MLOAD,
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 .GT,
   opAt 2604 (.Swap ⟨1, by decide⟩),
   opAt 2605 .SUB,
   opAt 2606 (.Dup ⟨3, by decide⟩),
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .LT,
   opAt 2609 (.Swap ⟨0, by decide⟩),
   opAt 2610 (.Dup ⟨4, by decide⟩),
   opAt 2611 (.Swap ⟨0, by decide⟩),
   opAt 2612 .SUB,
   opAt 2613 (.Dup ⟨3, by decide⟩),
   opAt 2614 .MSTORE,
   opAt 2615 .OR,
   opAt 2616 (.Swap ⟨1, by decide⟩),
   opAt 2617 .POP,
   pushAt 2618 1 31,
   opAt 2619 .NOT,
   opAt 2620 .ADD,
   pushAt 2621 2 2111,
   opAt 2622 (.Dup ⟨1, by decide⟩),
   opAt 2623 .GT,
   pushAt 2624 2 3449,
   opAt 2625 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2626 .POP,
   pushAt 2627 2 2080,
   opAt 2628 .MLOAD,
   opAt 2629 .SUB,
   pushAt 2630 2 2080,
   opAt 2631 .MSTORE,
   pushAt 2632 2 3431,
   opAt 2633 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2519 .JUMPDEST,
   opAt 2520 .NOT,
   opAt 2521 .ADD,
   pushAt 2522 2 3033,
   pushAt 2523 2 512,
   pushAt 2524 2 4330,
   opAt 2525 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2654 2 2688,
   opAt 2655 .MLOAD,
   pushAt 2656 2 1280,
   pushAt 2657 2 1024,
   opAt 2658 .MCOPY,
   pushAt 2659 2 2637,
   opAt 2660 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2794 = true :=
  Artifact.isValidJumpDest_index 2089 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2831 = true :=
  Artifact.isValidJumpDest_index 2112 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2848 = true :=
  Artifact.isValidJumpDest_index 2120 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2863 = true :=
  Artifact.isValidJumpDest_index 2128 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3033 = true :=
  Artifact.isValidJumpDest_index 2261 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3150 = true :=
  Artifact.isValidJumpDest_index 2342 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3364 = true :=
  Artifact.isValidJumpDest_index 2530 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3370 = true :=
  Artifact.isValidJumpDest_index 2534 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3431 = true :=
  Artifact.isValidJumpDest_index 2582 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3449 = true :=
  Artifact.isValidJumpDest_index 2594 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3358 = true :=
  Artifact.isValidJumpDest_index 2526 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3443 = true :=
  Artifact.isValidJumpDest_index 2590 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3345 = true :=
  Artifact.isValidJumpDest_index 2519 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3502 = true :=
  Artifact.isValidJumpDest_index 2634 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
