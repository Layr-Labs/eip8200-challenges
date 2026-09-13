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
  [opAt 2087 .JUMPDEST,
   opAt 2088 (.Dup ⟨0, by decide⟩),
   opAt 2089 (.Dup ⟨3, by decide⟩),
   opAt 2090 .EQ,
   pushAt 2091 0 0,
   opAt 2092 .MLOAD,
   pushAt 2093 1 255,
   opAt 2094 .SHR,
   opAt 2095 .AND,
   opAt 2096 .ISZERO,
   pushAt 2097 2 2838,
   opAt 2098 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2099 (.Dup ⟨0, by decide⟩),
   pushAt 2100 1 96,
   pushAt 2101 2 256,
   opAt 2102 .CALLDATACOPY,
   opAt 2103 (.Dup ⟨0, by decide⟩),
   pushAt 2104 1 96,
   pushAt 2105 2 2112,
   opAt 2106 .CALLDATACOPY,
   pushAt 2107 0 0,
   pushAt 2108 2 2080,
   opAt 2109 .MSTORE,
   pushAt 2110 2 2855,
   pushAt 2111 2 512,
   pushAt 2112 2 4333,
   opAt 2113 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2114 .JUMPDEST,
   pushAt 2115 1 1,
   pushAt 2116 2 1024,
   opAt 2117 .MSTORE,
   pushAt 2118 2 880,
   pushAt 2119 2 1024,
   pushAt 2120 2 1657,
   opAt 2121 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2122 .JUMPDEST,
   pushAt 2123 1 1,
   pushAt 2124 2 2752,
   opAt 2125 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2147 .POP,
   opAt 2148 .POP,
   pushAt 2149 0 0,
   opAt 2150 .MLOAD,
   opAt 2151 (.Dup ⟨0, by decide⟩),
   pushAt 2152 0 0,
   opAt 2153 .SUB,
   opAt 2154 (.Dup ⟨1, by decide⟩),
   opAt 2155 .AND,
   opAt 2156 (.Dup ⟨0, by decide⟩),
   pushAt 2157 2 1536,
   opAt 2158 .MSTORE,
   opAt 2159 (.Dup ⟨0, by decide⟩),
   opAt 2160 (.Dup ⟨2, by decide⟩),
   opAt 2161 .DIV,
   opAt 2162 (.Dup ⟨0, by decide⟩),
   pushAt 2163 2 1568,
   opAt 2164 .MSTORE,
   opAt 2165 (.Dup ⟨1, by decide⟩),
   opAt 2166 (.Dup ⟨0, by decide⟩),
   pushAt 2167 0 0,
   opAt 2168 .SUB,
   opAt 2169 .DIV,
   pushAt 2170 1 1,
   opAt 2171 .ADD,
   pushAt 2172 2 1600,
   opAt 2173 .MSTORE,
   opAt 2174 (.Dup ⟨0, by decide⟩),
   opAt 2175 (.Dup ⟨0, by decide⟩),
   pushAt 2176 0 0,
   opAt 2177 .SUB,
   opAt 2178 .MOD,
   pushAt 2179 2 1632,
   opAt 2180 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2181 (.Dup ⟨0, by decide⟩),
   pushAt 2182 1 3,
   opAt 2183 .MUL,
   pushAt 2184 1 2,
   opAt 2185 .XOR,
   opAt 2186 (.Dup ⟨0, by decide⟩),
   opAt 2187 (.Dup ⟨2, by decide⟩),
   opAt 2188 .MUL,
   pushAt 2189 1 2,
   opAt 2190 .SUB,
   opAt 2191 .MUL,
   opAt 2192 (.Dup ⟨0, by decide⟩),
   opAt 2193 (.Dup ⟨2, by decide⟩),
   opAt 2194 .MUL,
   pushAt 2195 1 2,
   opAt 2196 .SUB,
   opAt 2197 .MUL,
   opAt 2198 (.Dup ⟨0, by decide⟩),
   opAt 2199 (.Dup ⟨2, by decide⟩),
   opAt 2200 .MUL,
   pushAt 2201 1 2,
   opAt 2202 .SUB,
   opAt 2203 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2204 (.Dup ⟨0, by decide⟩),
   opAt 2205 (.Dup ⟨2, by decide⟩),
   opAt 2206 .MUL,
   pushAt 2207 1 2,
   opAt 2208 .SUB,
   opAt 2209 .MUL,
   opAt 2210 (.Dup ⟨0, by decide⟩),
   opAt 2211 (.Dup ⟨2, by decide⟩),
   opAt 2212 .MUL,
   pushAt 2213 1 2,
   opAt 2214 .SUB,
   opAt 2215 .MUL,
   opAt 2216 (.Dup ⟨0, by decide⟩),
   opAt 2217 (.Dup ⟨2, by decide⟩),
   opAt 2218 .MUL,
   pushAt 2219 1 2,
   opAt 2220 .SUB,
   opAt 2221 .MUL,
   pushAt 2222 2 1664,
   opAt 2223 .MSTORE,
   opAt 2224 .POP,
   opAt 2225 .POP,
   opAt 2226 .POP,
   opAt 2227 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2259 .JUMPDEST,
   opAt 2260 (.Dup ⟨0, by decide⟩),
   opAt 2261 .ISZERO,
   pushAt 2262 2 3499,
   opAt 2263 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2264 (.Dup ⟨1, by decide⟩),
   pushAt 2265 2 512,
   pushAt 2266 2 2080,
   opAt 2267 .MCOPY,
   pushAt 2268 0 0,
   pushAt 2269 2 2784,
   opAt 2270 .MLOAD,
   opAt 2271 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2272 2 512,
   opAt 2273 .MLOAD,
   pushAt 2274 2 1536,
   opAt 2275 .MLOAD,
   opAt 2276 (.Dup ⟨1, by decide⟩),
   opAt 2277 .DIV,
   opAt 2278 (.Swap ⟨0, by decide⟩),
   pushAt 2279 2 1600,
   opAt 2280 .MLOAD,
   opAt 2281 .MUL,
   pushAt 2282 2 1536,
   opAt 2283 .MLOAD,
   pushAt 2284 2 544,
   opAt 2285 .MLOAD,
   opAt 2286 .DIV,
   opAt 2287 .ADD,
   pushAt 2288 2 1568,
   opAt 2289 .MLOAD,
   opAt 2290 (.Dup ⟨0, by decide⟩),
   pushAt 2291 2 1632,
   opAt 2292 .MLOAD,
   opAt 2293 (.Dup ⟨4, by decide⟩),
   opAt 2294 .MULMOD,
   opAt 2295 (.Dup ⟨2, by decide⟩),
   opAt 2296 .ADDMOD,
   opAt 2297 (.Swap ⟨0, by decide⟩),
   opAt 2298 .SUB,
   pushAt 2299 2 1664,
   opAt 2300 .MLOAD,
   opAt 2301 .MUL,
   opAt 2302 (.Dup ⟨0, by decide⟩),
   pushAt 2303 0 0,
   opAt 2304 .MLOAD,
   opAt 2305 .MUL,
   pushAt 2306 2 544,
   opAt 2307 .MLOAD,
   opAt 2308 .SUB,
   pushAt 2309 1 32,
   opAt 2310 .MLOAD,
   pushAt 2311 1 128,
   opAt 2312 .SHR,
   opAt 2313 (.Dup ⟨2, by decide⟩),
   pushAt 2314 1 128,
   opAt 2315 .SHR,
   opAt 2316 .MUL,
   opAt 2317 .GT,
   opAt 2318 (.Swap ⟨0, by decide⟩),
   opAt 2319 .SUB,
   opAt 2320 (.Swap ⟨0, by decide⟩),
   pushAt 2321 2 1568,
   opAt 2322 .MLOAD,
   opAt 2323 .GT,
   opAt 2324 .ISZERO,
   pushAt 2325 0 0,
   opAt 2326 .SUB,
   opAt 2327 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2328 0 0,
   pushAt 2329 1 31,
   opAt 2330 .NOT,
   pushAt 2331 0 0,
   opAt 2332 .NOT,
   pushAt 2333 2 2784,
   opAt 2334 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2338 .JUMPDEST,
   pushAt 2339 2 832,
   opAt 2340 (.Dup ⟨1, by decide⟩),
   opAt 2341 .SUB,
   opAt 2342 .MLOAD,
   opAt 2343 (.Dup ⟨2, by decide⟩),
   opAt 2344 (.Dup ⟨6, by decide⟩),
   opAt 2345 (.Dup ⟨2, by decide⟩),
   opAt 2346 .MUL,
   opAt 2347 (.Swap ⟨1, by decide⟩),
   opAt 2348 (.Dup ⟨7, by decide⟩),
   opAt 2349 .MULMOD,
   opAt 2350 (.Dup ⟨1, by decide⟩),
   opAt 2351 (.Dup ⟨1, by decide⟩),
   opAt 2352 .LT,
   opAt 2353 .SUB,
   opAt 2354 (.Dup ⟨5, by decide⟩),
   opAt 2355 (.Dup ⟨2, by decide⟩),
   opAt 2356 .ADD,
   opAt 2357 (.Dup ⟨0, by decide⟩),
   opAt 2358 (.Swap ⟨6, by decide⟩),
   opAt 2359 .GT,
   opAt 2360 .SUB,
   opAt 2361 .SUB,
   opAt 2362 (.Dup ⟨4, by decide⟩),
   opAt 2363 (.Dup ⟨2, by decide⟩),
   opAt 2364 .MLOAD,
   opAt 2365 .ADD,
   opAt 2366 (.Dup ⟨0, by decide⟩),
   opAt 2367 (.Swap ⟨5, by decide⟩),
   opAt 2368 .GT,
   opAt 2369 .ADD,
   opAt 2370 (.Swap ⟨3, by decide⟩),
   opAt 2371 (.Dup ⟨1, by decide⟩),
   opAt 2372 .MSTORE,
   opAt 2373 (.Dup ⟨2, by decide⟩),
   opAt 2374 .ADD,
   pushAt 2486 2 2080,
   opAt 2487 (.Dup ⟨1, by decide⟩),
   opAt 2488 .GT,
   pushAt 2489 2 3147,
   opAt 2490 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2491 .POP,
   opAt 2492 .POP,
   opAt 2493 .POP,
   pushAt 2494 2 2080,
   opAt 2495 .MLOAD,
   opAt 2496 (.Dup ⟨1, by decide⟩),
   opAt 2497 .ADD,
   opAt 2498 (.Dup ⟨0, by decide⟩),
   opAt 2499 (.Swap ⟨1, by decide⟩),
   opAt 2500 .GT,
   opAt 2501 (.Dup ⟨1, by decide⟩),
   opAt 2502 (.Dup ⟨3, by decide⟩),
   opAt 2503 .GT,
   opAt 2504 .GT,
   opAt 2505 (.Swap ⟨1, by decide⟩),
   opAt 2506 (.Swap ⟨0, by decide⟩),
   opAt 2507 .SUB,
   opAt 2508 (.Dup ⟨0, by decide⟩),
   pushAt 2509 2 2080,
   opAt 2510 .MSTORE,
   opAt 2511 (.Dup ⟨1, by decide⟩),
   opAt 2512 .OR,
   pushAt 2513 2 3355,
   opAt 2514 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2522 .JUMPDEST,
   opAt 2523 .ISZERO,
   pushAt 2524 2 3440,
   opAt 2525 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2526 .JUMPDEST,
   pushAt 2527 0 0,
   pushAt 2528 2 2784,
   opAt 2529 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2530 .JUMPDEST,
   opAt 2531 (.Dup ⟨0, by decide⟩),
   opAt 2532 .MLOAD,
   opAt 2533 (.Dup ⟨1, by decide⟩),
   pushAt 2534 2 2112,
   opAt 2535 (.Swap ⟨0, by decide⟩),
   opAt 2536 .SUB,
   opAt 2537 .MLOAD,
   opAt 2538 (.Dup ⟨1, by decide⟩),
   opAt 2539 .ADD,
   opAt 2540 (.Dup ⟨0, by decide⟩),
   opAt 2541 (.Dup ⟨2, by decide⟩),
   opAt 2542 .GT,
   opAt 2543 (.Swap ⟨1, by decide⟩),
   opAt 2544 .POP,
   opAt 2545 (.Dup ⟨3, by decide⟩),
   opAt 2546 .ADD,
   opAt 2547 (.Dup ⟨0, by decide⟩),
   opAt 2548 (.Dup ⟨4, by decide⟩),
   opAt 2549 .GT,
   opAt 2550 (.Swap ⟨3, by decide⟩),
   opAt 2551 .POP,
   opAt 2552 (.Dup ⟨2, by decide⟩),
   opAt 2553 .MSTORE,
   opAt 2554 (.Swap ⟨0, by decide⟩),
   opAt 2555 (.Swap ⟨1, by decide⟩),
   opAt 2556 .OR,
   opAt 2557 (.Swap ⟨0, by decide⟩),
   pushAt 2558 1 31,
   opAt 2559 .NOT,
   opAt 2560 .ADD,
   pushAt 2561 2 2111,
   opAt 2562 (.Dup ⟨1, by decide⟩),
   opAt 2563 .GT,
   pushAt 2564 2 3367,
   opAt 2565 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2566 .POP,
   pushAt 2567 2 2080,
   opAt 2568 .MLOAD,
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .ADD,
   opAt 2571 (.Dup ⟨0, by decide⟩),
   pushAt 2572 2 2080,
   opAt 2573 .MSTORE,
   opAt 2574 .LT,
   opAt 2575 .ISZERO,
   pushAt 2576 2 3361,
   opAt 2577 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .JUMPDEST,
   pushAt 2579 2 2080,
   opAt 2580 .MLOAD,
   opAt 2581 (.Dup ⟨0, by decide⟩),
   opAt 2582 .ISZERO,
   pushAt 2583 2 3342,
   opAt 2584 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .JUMPDEST,
   pushAt 2579 2 2080,
   opAt 2580 .MLOAD,
   opAt 2581 (.Dup ⟨0, by decide⟩),
   opAt 2582 .ISZERO,
   pushAt 2583 2 3342,
   opAt 2584 .JUMPI,
   opAt 2585 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2586 .JUMPDEST,
   pushAt 2587 0 0,
   pushAt 2588 2 2784,
   opAt 2589 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2590 .JUMPDEST,
   opAt 2591 (.Dup ⟨0, by decide⟩),
   opAt 2592 .MLOAD,
   pushAt 2593 2 2112,
   opAt 2594 (.Dup ⟨2, by decide⟩),
   opAt 2595 .SUB,
   opAt 2596 .MLOAD,
   opAt 2597 (.Dup ⟨1, by decide⟩),
   opAt 2598 (.Dup ⟨1, by decide⟩),
   opAt 2599 .GT,
   opAt 2600 (.Swap ⟨1, by decide⟩),
   opAt 2601 .SUB,
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 (.Dup ⟨1, by decide⟩),
   opAt 2604 .LT,
   opAt 2605 (.Swap ⟨0, by decide⟩),
   opAt 2606 (.Dup ⟨4, by decide⟩),
   opAt 2607 (.Swap ⟨0, by decide⟩),
   opAt 2608 .SUB,
   opAt 2609 (.Dup ⟨3, by decide⟩),
   opAt 2610 .MSTORE,
   opAt 2611 .OR,
   opAt 2612 (.Swap ⟨1, by decide⟩),
   opAt 2613 .POP,
   pushAt 2614 1 31,
   opAt 2615 .NOT,
   opAt 2616 .ADD,
   pushAt 2617 2 2111,
   opAt 2618 (.Dup ⟨1, by decide⟩),
   opAt 2619 .GT,
   pushAt 2620 2 3446,
   opAt 2621 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2622 .POP,
   pushAt 2623 2 2080,
   opAt 2624 .MLOAD,
   opAt 2625 .SUB,
   pushAt 2626 2 2080,
   opAt 2627 .MSTORE,
   pushAt 2628 2 3428,
   opAt 2629 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2515 .JUMPDEST,
   opAt 2516 .NOT,
   opAt 2517 .ADD,
   pushAt 2518 2 3032,
   pushAt 2519 2 512,
   pushAt 2520 2 4333,
   opAt 2521 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2650 2 2688,
   opAt 2651 .MLOAD,
   pushAt 2652 2 1280,
   pushAt 2653 2 1024,
   opAt 2654 .MCOPY,
   pushAt 2655 2 2637,
   opAt 2656 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2794 = true :=
  Artifact.isValidJumpDest_index 2087 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2838 = true :=
  Artifact.isValidJumpDest_index 2114 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2855 = true :=
  Artifact.isValidJumpDest_index 2122 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2862 = true :=
  Artifact.isValidJumpDest_index 2126 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3032 = true :=
  Artifact.isValidJumpDest_index 2259 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3147 = true :=
  Artifact.isValidJumpDest_index 2338 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3361 = true :=
  Artifact.isValidJumpDest_index 2526 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3367 = true :=
  Artifact.isValidJumpDest_index 2530 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3428 = true :=
  Artifact.isValidJumpDest_index 2578 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3446 = true :=
  Artifact.isValidJumpDest_index 2590 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3355 = true :=
  Artifact.isValidJumpDest_index 2522 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3440 = true :=
  Artifact.isValidJumpDest_index 2586 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3342 = true :=
  Artifact.isValidJumpDest_index 2515 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3499 = true :=
  Artifact.isValidJumpDest_index 2630 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
