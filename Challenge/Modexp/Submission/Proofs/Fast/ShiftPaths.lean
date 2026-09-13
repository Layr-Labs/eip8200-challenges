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
  [opAt 2084 .JUMPDEST,
   opAt 2085 (.Dup ⟨0, by decide⟩),
   opAt 2086 (.Dup ⟨3, by decide⟩),
   opAt 2087 .EQ,
   pushAt 2088 0 0,
   opAt 2089 .MLOAD,
   pushAt 2090 1 255,
   opAt 2091 .SHR,
   opAt 2092 .AND,
   opAt 2093 .ISZERO,
   pushAt 2094 2 2839,
   opAt 2095 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2096 (.Dup ⟨0, by decide⟩),
   pushAt 2097 1 96,
   pushAt 2098 2 256,
   opAt 2099 .CALLDATACOPY,
   opAt 2100 (.Dup ⟨0, by decide⟩),
   pushAt 2101 1 96,
   pushAt 2102 2 2112,
   opAt 2103 .CALLDATACOPY,
   pushAt 2104 0 0,
   pushAt 2105 2 2080,
   opAt 2106 .MSTORE,
   pushAt 2107 2 2856,
   pushAt 2108 2 512,
   pushAt 2109 2 4338,
   opAt 2110 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2111 .JUMPDEST,
   pushAt 2112 1 1,
   pushAt 2113 2 1024,
   opAt 2114 .MSTORE,
   pushAt 2115 2 881,
   pushAt 2116 2 1024,
   pushAt 2117 2 1658,
   opAt 2118 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2119 .JUMPDEST,
   pushAt 2120 1 1,
   pushAt 2121 2 2752,
   opAt 2122 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2144 .POP,
   opAt 2145 .POP,
   pushAt 2146 0 0,
   opAt 2147 .MLOAD,
   opAt 2148 (.Dup ⟨0, by decide⟩),
   pushAt 2149 0 0,
   opAt 2150 .SUB,
   opAt 2151 (.Dup ⟨1, by decide⟩),
   opAt 2152 .AND,
   opAt 2153 (.Dup ⟨0, by decide⟩),
   pushAt 2154 2 1536,
   opAt 2155 .MSTORE,
   opAt 2156 (.Dup ⟨0, by decide⟩),
   opAt 2157 (.Dup ⟨2, by decide⟩),
   opAt 2158 .DIV,
   opAt 2159 (.Dup ⟨0, by decide⟩),
   pushAt 2160 2 1568,
   opAt 2161 .MSTORE,
   opAt 2162 (.Dup ⟨1, by decide⟩),
   opAt 2163 (.Dup ⟨0, by decide⟩),
   pushAt 2164 0 0,
   opAt 2165 .SUB,
   opAt 2166 .DIV,
   pushAt 2167 1 1,
   opAt 2168 .ADD,
   pushAt 2169 2 1600,
   opAt 2170 .MSTORE,
   opAt 2171 (.Dup ⟨0, by decide⟩),
   opAt 2172 (.Dup ⟨0, by decide⟩),
   pushAt 2173 0 0,
   opAt 2174 .SUB,
   opAt 2175 .MOD,
   pushAt 2176 2 1632,
   opAt 2177 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2178 (.Dup ⟨0, by decide⟩),
   pushAt 2179 1 3,
   opAt 2180 .MUL,
   pushAt 2181 1 2,
   opAt 2182 .XOR,
   opAt 2183 (.Dup ⟨0, by decide⟩),
   opAt 2184 (.Dup ⟨2, by decide⟩),
   opAt 2185 .MUL,
   pushAt 2186 1 2,
   opAt 2187 .SUB,
   opAt 2188 .MUL,
   opAt 2189 (.Dup ⟨0, by decide⟩),
   opAt 2190 (.Dup ⟨2, by decide⟩),
   opAt 2191 .MUL,
   pushAt 2192 1 2,
   opAt 2193 .SUB,
   opAt 2194 .MUL,
   opAt 2195 (.Dup ⟨0, by decide⟩),
   opAt 2196 (.Dup ⟨2, by decide⟩),
   opAt 2197 .MUL,
   pushAt 2198 1 2,
   opAt 2199 .SUB,
   opAt 2200 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2201 (.Dup ⟨0, by decide⟩),
   opAt 2202 (.Dup ⟨2, by decide⟩),
   opAt 2203 .MUL,
   pushAt 2204 1 2,
   opAt 2205 .SUB,
   opAt 2206 .MUL,
   opAt 2207 (.Dup ⟨0, by decide⟩),
   opAt 2208 (.Dup ⟨2, by decide⟩),
   opAt 2209 .MUL,
   pushAt 2210 1 2,
   opAt 2211 .SUB,
   opAt 2212 .MUL,
   opAt 2213 (.Dup ⟨0, by decide⟩),
   opAt 2214 (.Dup ⟨2, by decide⟩),
   opAt 2215 .MUL,
   pushAt 2216 1 2,
   opAt 2217 .SUB,
   opAt 2218 .MUL,
   pushAt 2219 2 1664,
   opAt 2220 .MSTORE,
   opAt 2221 .POP,
   opAt 2222 .POP,
   opAt 2223 .POP,
   opAt 2224 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2256 .JUMPDEST,
   opAt 2257 (.Dup ⟨0, by decide⟩),
   opAt 2258 .ISZERO,
   pushAt 2259 2 3504,
   opAt 2260 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2261 (.Dup ⟨1, by decide⟩),
   pushAt 2262 2 512,
   pushAt 2263 2 2080,
   opAt 2264 .MCOPY,
   pushAt 2265 0 0,
   pushAt 2266 2 2784,
   opAt 2267 .MLOAD,
   opAt 2268 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2269 2 512,
   opAt 2270 .MLOAD,
   pushAt 2271 2 1536,
   opAt 2272 .MLOAD,
   opAt 2273 (.Dup ⟨1, by decide⟩),
   opAt 2274 .DIV,
   opAt 2275 (.Swap ⟨0, by decide⟩),
   opAt 2276 .JUMPDEST,
   opAt 2277 .JUMPDEST,
   pushAt 2278 2 1600,
   opAt 2279 .MLOAD,
   opAt 2280 .MUL,
   pushAt 2281 2 544,
   opAt 2282 .MLOAD,
   pushAt 2283 2 1536,
   opAt 2284 .MLOAD,
   opAt 2285 (.Swap ⟨0, by decide⟩),
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
   pushAt 2331 2 2784,
   opAt 2332 .MLOAD,
   pushAt 2333 0 0,
   opAt 2334 .NOT,
   opAt 2335 (.Swap ⟨0, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2339 .JUMPDEST,
   pushAt 2340 2 832,
   opAt 2341 (.Dup ⟨1, by decide⟩),
   opAt 2342 .SUB,
   opAt 2343 .MLOAD,
   opAt 2344 (.Dup ⟨2, by decide⟩),
   opAt 2345 (.Dup ⟨6, by decide⟩),
   opAt 2346 (.Dup ⟨2, by decide⟩),
   opAt 2347 .MUL,
   opAt 2348 (.Swap ⟨1, by decide⟩),
   opAt 2349 (.Dup ⟨7, by decide⟩),
   opAt 2350 .MULMOD,
   opAt 2351 (.Dup ⟨1, by decide⟩),
   opAt 2352 (.Dup ⟨1, by decide⟩),
   opAt 2353 .LT,
   opAt 2354 .SUB,
   opAt 2355 (.Dup ⟨5, by decide⟩),
   opAt 2356 (.Dup ⟨2, by decide⟩),
   opAt 2357 .ADD,
   opAt 2358 (.Dup ⟨0, by decide⟩),
   opAt 2359 (.Swap ⟨6, by decide⟩),
   opAt 2360 .GT,
   opAt 2361 .SUB,
   opAt 2362 .SUB,
   opAt 2363 (.Dup ⟨4, by decide⟩),
   opAt 2364 (.Dup ⟨2, by decide⟩),
   opAt 2365 .MLOAD,
   opAt 2366 .ADD,
   opAt 2367 (.Dup ⟨0, by decide⟩),
   opAt 2368 (.Swap ⟨5, by decide⟩),
   opAt 2369 .GT,
   opAt 2370 .ADD,
   opAt 2371 (.Swap ⟨3, by decide⟩),
   opAt 2372 (.Dup ⟨1, by decide⟩),
   opAt 2373 .MSTORE,
   opAt 2374 (.Dup ⟨2, by decide⟩),
   opAt 2375 .ADD,
   pushAt 2487 2 2080,
   opAt 2488 (.Dup ⟨1, by decide⟩),
   opAt 2489 .GT,
   pushAt 2490 2 3152,
   opAt 2491 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2492 .POP,
   opAt 2493 .POP,
   opAt 2494 .POP,
   pushAt 2495 2 2080,
   opAt 2496 .MLOAD,
   opAt 2497 (.Dup ⟨1, by decide⟩),
   opAt 2498 .ADD,
   opAt 2499 (.Dup ⟨0, by decide⟩),
   opAt 2500 (.Swap ⟨1, by decide⟩),
   opAt 2501 .GT,
   opAt 2502 (.Dup ⟨1, by decide⟩),
   opAt 2503 (.Dup ⟨3, by decide⟩),
   opAt 2504 .GT,
   opAt 2505 .GT,
   opAt 2506 (.Swap ⟨1, by decide⟩),
   opAt 2507 (.Swap ⟨0, by decide⟩),
   opAt 2508 .SUB,
   opAt 2509 (.Dup ⟨0, by decide⟩),
   pushAt 2510 2 2080,
   opAt 2511 .MSTORE,
   opAt 2512 (.Dup ⟨1, by decide⟩),
   opAt 2513 .OR,
   pushAt 2514 2 3360,
   opAt 2515 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2523 .JUMPDEST,
   opAt 2524 .ISZERO,
   pushAt 2525 2 3445,
   opAt 2526 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2527 .JUMPDEST,
   pushAt 2528 0 0,
   pushAt 2529 2 2784,
   opAt 2530 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2531 .JUMPDEST,
   opAt 2532 (.Dup ⟨0, by decide⟩),
   opAt 2533 .MLOAD,
   opAt 2534 (.Dup ⟨1, by decide⟩),
   pushAt 2535 2 2112,
   opAt 2536 (.Swap ⟨0, by decide⟩),
   opAt 2537 .SUB,
   opAt 2538 .MLOAD,
   opAt 2539 (.Dup ⟨1, by decide⟩),
   opAt 2540 .ADD,
   opAt 2541 (.Dup ⟨0, by decide⟩),
   opAt 2542 (.Dup ⟨2, by decide⟩),
   opAt 2543 .GT,
   opAt 2544 (.Swap ⟨1, by decide⟩),
   opAt 2545 .POP,
   opAt 2546 (.Dup ⟨3, by decide⟩),
   opAt 2547 .ADD,
   opAt 2548 (.Dup ⟨0, by decide⟩),
   opAt 2549 (.Dup ⟨4, by decide⟩),
   opAt 2550 .GT,
   opAt 2551 (.Swap ⟨3, by decide⟩),
   opAt 2552 .POP,
   opAt 2553 (.Dup ⟨2, by decide⟩),
   opAt 2554 .MSTORE,
   opAt 2555 (.Swap ⟨0, by decide⟩),
   opAt 2556 (.Swap ⟨1, by decide⟩),
   opAt 2557 .OR,
   opAt 2558 (.Swap ⟨0, by decide⟩),
   pushAt 2559 1 31,
   opAt 2560 .NOT,
   opAt 2561 .ADD,
   pushAt 2562 2 2111,
   opAt 2563 (.Dup ⟨1, by decide⟩),
   opAt 2564 .GT,
   pushAt 2565 2 3372,
   opAt 2566 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2567 .POP,
   pushAt 2568 2 2080,
   opAt 2569 .MLOAD,
   opAt 2570 (.Dup ⟨1, by decide⟩),
   opAt 2571 .ADD,
   opAt 2572 (.Dup ⟨0, by decide⟩),
   pushAt 2573 2 2080,
   opAt 2574 .MSTORE,
   opAt 2575 .LT,
   opAt 2576 .ISZERO,
   pushAt 2577 2 3366,
   opAt 2578 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .JUMPDEST,
   pushAt 2580 2 2080,
   opAt 2581 .MLOAD,
   opAt 2582 (.Dup ⟨0, by decide⟩),
   opAt 2583 .ISZERO,
   pushAt 2584 2 3347,
   opAt 2585 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .JUMPDEST,
   pushAt 2580 2 2080,
   opAt 2581 .MLOAD,
   opAt 2582 (.Dup ⟨0, by decide⟩),
   opAt 2583 .ISZERO,
   pushAt 2584 2 3347,
   opAt 2585 .JUMPI,
   opAt 2586 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2587 .JUMPDEST,
   pushAt 2588 0 0,
   pushAt 2589 2 2784,
   opAt 2590 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2591 .JUMPDEST,
   opAt 2592 (.Dup ⟨0, by decide⟩),
   opAt 2593 .MLOAD,
   pushAt 2594 2 2112,
   opAt 2595 (.Dup ⟨2, by decide⟩),
   opAt 2596 .SUB,
   opAt 2597 .MLOAD,
   opAt 2598 (.Dup ⟨1, by decide⟩),
   opAt 2599 (.Dup ⟨1, by decide⟩),
   opAt 2600 .GT,
   opAt 2601 (.Swap ⟨1, by decide⟩),
   opAt 2602 .SUB,
   opAt 2603 (.Dup ⟨3, by decide⟩),
   opAt 2604 (.Dup ⟨1, by decide⟩),
   opAt 2605 .LT,
   opAt 2606 (.Swap ⟨0, by decide⟩),
   opAt 2607 (.Dup ⟨4, by decide⟩),
   opAt 2608 (.Swap ⟨0, by decide⟩),
   opAt 2609 .SUB,
   opAt 2610 (.Dup ⟨3, by decide⟩),
   opAt 2611 .MSTORE,
   opAt 2612 .OR,
   opAt 2613 (.Swap ⟨1, by decide⟩),
   opAt 2614 .POP,
   pushAt 2615 1 31,
   opAt 2616 .NOT,
   opAt 2617 .ADD,
   pushAt 2618 2 2111,
   opAt 2619 (.Dup ⟨1, by decide⟩),
   opAt 2620 .GT,
   pushAt 2621 2 3451,
   opAt 2622 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2623 .POP,
   pushAt 2624 2 2080,
   opAt 2625 .MLOAD,
   opAt 2626 .SUB,
   pushAt 2627 2 2080,
   opAt 2628 .MSTORE,
   pushAt 2629 2 3433,
   opAt 2630 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2516 .JUMPDEST,
   opAt 2517 .NOT,
   opAt 2518 .ADD,
   pushAt 2519 2 3033,
   pushAt 2520 2 512,
   pushAt 2521 2 4338,
   opAt 2522 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2651 2 2688,
   opAt 2652 .MLOAD,
   pushAt 2653 2 1280,
   pushAt 2654 2 1024,
   opAt 2655 .MCOPY,
   pushAt 2656 2 2638,
   opAt 2657 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2795 = true :=
  Artifact.isValidJumpDest_index 2084 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2839 = true :=
  Artifact.isValidJumpDest_index 2111 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2856 = true :=
  Artifact.isValidJumpDest_index 2119 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2863 = true :=
  Artifact.isValidJumpDest_index 2123 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3033 = true :=
  Artifact.isValidJumpDest_index 2256 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3152 = true :=
  Artifact.isValidJumpDest_index 2339 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3366 = true :=
  Artifact.isValidJumpDest_index 2527 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3372 = true :=
  Artifact.isValidJumpDest_index 2531 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3433 = true :=
  Artifact.isValidJumpDest_index 2579 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3451 = true :=
  Artifact.isValidJumpDest_index 2591 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3360 = true :=
  Artifact.isValidJumpDest_index 2523 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3445 = true :=
  Artifact.isValidJumpDest_index 2587 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3347 = true :=
  Artifact.isValidJumpDest_index 2516 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3504 = true :=
  Artifact.isValidJumpDest_index 2631 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
