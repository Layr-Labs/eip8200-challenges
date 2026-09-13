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
  [opAt 2091 .JUMPDEST,
   opAt 2092 (.Dup ⟨0, by decide⟩),
   opAt 2093 (.Dup ⟨3, by decide⟩),
   opAt 2094 .EQ,
   pushAt 2095 0 0,
   opAt 2096 .MLOAD,
   pushAt 2097 1 255,
   opAt 2098 .SHR,
   opAt 2099 .AND,
   opAt 2100 .ISZERO,
   pushAt 2101 2 2844,
   opAt 2102 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2103 (.Dup ⟨0, by decide⟩),
   pushAt 2104 1 96,
   pushAt 2105 2 256,
   opAt 2106 .CALLDATACOPY,
   opAt 2107 (.Dup ⟨0, by decide⟩),
   pushAt 2108 1 96,
   pushAt 2109 2 2112,
   opAt 2110 .CALLDATACOPY,
   pushAt 2111 0 0,
   pushAt 2112 2 2080,
   opAt 2113 .MSTORE,
   pushAt 2114 2 2861,
   pushAt 2115 2 512,
   pushAt 2116 2 4349,
   opAt 2117 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2118 .JUMPDEST,
   pushAt 2119 1 1,
   pushAt 2120 2 1024,
   opAt 2121 .MSTORE,
   pushAt 2122 2 884,
   pushAt 2123 2 1024,
   pushAt 2124 2 1662,
   opAt 2125 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2126 .JUMPDEST,
   pushAt 2127 1 1,
   pushAt 2128 2 2752,
   opAt 2129 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2151 .JUMPDEST,
   opAt 2152 .POP,
   opAt 2153 .POP,
   pushAt 2154 0 0,
   opAt 2155 .MLOAD,
   opAt 2156 (.Dup ⟨0, by decide⟩),
   pushAt 2157 0 0,
   opAt 2158 .SUB,
   opAt 2159 (.Dup ⟨1, by decide⟩),
   opAt 2160 .AND,
   opAt 2161 (.Dup ⟨0, by decide⟩),
   pushAt 2162 2 1536,
   opAt 2163 .MSTORE,
   opAt 2164 (.Dup ⟨0, by decide⟩),
   opAt 2165 (.Dup ⟨2, by decide⟩),
   opAt 2166 .DIV,
   opAt 2167 (.Dup ⟨0, by decide⟩),
   pushAt 2168 2 1568,
   opAt 2169 .MSTORE,
   opAt 2170 (.Dup ⟨1, by decide⟩),
   opAt 2171 (.Dup ⟨0, by decide⟩),
   pushAt 2172 0 0,
   opAt 2173 .SUB,
   opAt 2174 .DIV,
   pushAt 2175 1 1,
   opAt 2176 .ADD,
   pushAt 2177 2 1600,
   opAt 2178 .MSTORE,
   opAt 2179 (.Dup ⟨0, by decide⟩),
   opAt 2180 (.Dup ⟨0, by decide⟩),
   pushAt 2181 0 0,
   opAt 2182 .SUB,
   opAt 2183 .MOD,
   pushAt 2184 2 1632,
   opAt 2185 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2186 (.Dup ⟨0, by decide⟩),
   pushAt 2187 1 3,
   opAt 2188 .MUL,
   pushAt 2189 1 2,
   opAt 2190 .XOR,
   opAt 2191 (.Dup ⟨0, by decide⟩),
   opAt 2192 (.Dup ⟨2, by decide⟩),
   opAt 2193 .MUL,
   pushAt 2194 1 2,
   opAt 2195 .SUB,
   opAt 2196 .MUL,
   opAt 2197 (.Dup ⟨0, by decide⟩),
   opAt 2198 (.Dup ⟨2, by decide⟩),
   opAt 2199 .MUL,
   pushAt 2200 1 2,
   opAt 2201 .SUB,
   opAt 2202 .MUL,
   opAt 2203 (.Dup ⟨0, by decide⟩),
   opAt 2204 (.Dup ⟨2, by decide⟩),
   opAt 2205 .MUL,
   pushAt 2206 1 2,
   opAt 2207 .SUB,
   opAt 2208 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2209 (.Dup ⟨0, by decide⟩),
   opAt 2210 (.Dup ⟨2, by decide⟩),
   opAt 2211 .MUL,
   pushAt 2212 1 2,
   opAt 2213 .SUB,
   opAt 2214 .MUL,
   opAt 2215 (.Dup ⟨0, by decide⟩),
   opAt 2216 (.Dup ⟨2, by decide⟩),
   opAt 2217 .MUL,
   pushAt 2218 1 2,
   opAt 2219 .SUB,
   opAt 2220 .MUL,
   opAt 2221 (.Dup ⟨0, by decide⟩),
   opAt 2222 (.Dup ⟨2, by decide⟩),
   opAt 2223 .MUL,
   pushAt 2224 1 2,
   opAt 2225 .SUB,
   opAt 2226 .MUL,
   pushAt 2227 2 1664,
   opAt 2228 .MSTORE,
   opAt 2229 .POP,
   opAt 2230 .POP,
   opAt 2231 .POP,
   opAt 2232 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2264 .JUMPDEST,
   opAt 2265 (.Dup ⟨0, by decide⟩),
   opAt 2266 .ISZERO,
   pushAt 2267 2 3510,
   opAt 2268 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2269 (.Dup ⟨1, by decide⟩),
   pushAt 2270 2 512,
   pushAt 2271 2 2080,
   opAt 2272 .MCOPY,
   pushAt 2273 0 0,
   pushAt 2274 2 2784,
   opAt 2275 .MLOAD,
   opAt 2276 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2277 2 512,
   opAt 2278 .MLOAD,
   pushAt 2279 2 1536,
   opAt 2280 .MLOAD,
   opAt 2281 (.Dup ⟨1, by decide⟩),
   opAt 2282 .DIV,
   opAt 2283 (.Swap ⟨0, by decide⟩),
   opAt 2284 .JUMPDEST,
   opAt 2285 .JUMPDEST,
   pushAt 2286 2 1600,
   opAt 2287 .MLOAD,
   opAt 2288 .MUL,
   pushAt 2289 2 544,
   opAt 2290 .MLOAD,
   pushAt 2291 2 1536,
   opAt 2292 .MLOAD,
   opAt 2293 (.Swap ⟨0, by decide⟩),
   opAt 2294 .DIV,
   opAt 2295 .ADD,
   pushAt 2296 2 1568,
   opAt 2297 .MLOAD,
   opAt 2298 (.Dup ⟨0, by decide⟩),
   pushAt 2299 2 1632,
   opAt 2300 .MLOAD,
   opAt 2301 (.Dup ⟨4, by decide⟩),
   opAt 2302 .MULMOD,
   opAt 2303 (.Dup ⟨2, by decide⟩),
   opAt 2304 .ADDMOD,
   opAt 2305 (.Swap ⟨0, by decide⟩),
   opAt 2306 .SUB,
   pushAt 2307 2 1664,
   opAt 2308 .MLOAD,
   opAt 2309 .MUL,
   opAt 2310 (.Dup ⟨0, by decide⟩),
   pushAt 2311 0 0,
   opAt 2312 .MLOAD,
   opAt 2313 .MUL,
   pushAt 2314 2 544,
   opAt 2315 .MLOAD,
   opAt 2316 .SUB,
   pushAt 2317 1 32,
   opAt 2318 .MLOAD,
   pushAt 2319 1 128,
   opAt 2320 .SHR,
   opAt 2321 (.Dup ⟨2, by decide⟩),
   pushAt 2322 1 128,
   opAt 2323 .SHR,
   opAt 2324 .MUL,
   opAt 2325 .GT,
   opAt 2326 (.Swap ⟨0, by decide⟩),
   opAt 2327 .SUB,
   opAt 2328 (.Swap ⟨0, by decide⟩),
   pushAt 2329 2 1568,
   opAt 2330 .MLOAD,
   opAt 2331 .GT,
   opAt 2332 .ISZERO,
   pushAt 2333 0 0,
   opAt 2334 .SUB,
   opAt 2335 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2336 0 0,
   pushAt 2337 1 31,
   opAt 2338 .NOT,
   pushAt 2339 2 2784,
   opAt 2340 .MLOAD,
   pushAt 2341 0 0,
   opAt 2342 .NOT,
   opAt 2343 (.Swap ⟨0, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2347 .JUMPDEST,
   pushAt 2348 2 832,
   opAt 2349 (.Dup ⟨1, by decide⟩),
   opAt 2350 .SUB,
   opAt 2351 .MLOAD,
   opAt 2352 (.Dup ⟨2, by decide⟩),
   opAt 2353 (.Dup ⟨6, by decide⟩),
   opAt 2354 (.Dup ⟨2, by decide⟩),
   opAt 2355 .MUL,
   opAt 2356 (.Swap ⟨1, by decide⟩),
   opAt 2357 (.Dup ⟨7, by decide⟩),
   opAt 2358 .MULMOD,
   opAt 2359 (.Dup ⟨1, by decide⟩),
   opAt 2360 (.Dup ⟨1, by decide⟩),
   opAt 2361 .LT,
   opAt 2362 .SUB,
   opAt 2363 (.Dup ⟨5, by decide⟩),
   opAt 2364 (.Dup ⟨2, by decide⟩),
   opAt 2365 .ADD,
   opAt 2366 (.Dup ⟨0, by decide⟩),
   opAt 2367 (.Swap ⟨6, by decide⟩),
   opAt 2368 .GT,
   opAt 2369 .SUB,
   opAt 2370 .SUB,
   opAt 2371 (.Dup ⟨4, by decide⟩),
   opAt 2372 (.Dup ⟨2, by decide⟩),
   opAt 2373 .MLOAD,
   opAt 2374 .ADD,
   opAt 2375 (.Dup ⟨0, by decide⟩),
   opAt 2376 (.Swap ⟨5, by decide⟩),
   opAt 2377 .GT,
   opAt 2378 .ADD,
   opAt 2379 (.Swap ⟨3, by decide⟩),
   opAt 2380 (.Dup ⟨1, by decide⟩),
   opAt 2381 .MSTORE,
   opAt 2382 (.Dup ⟨2, by decide⟩),
   opAt 2383 .ADD,
   pushAt 2495 2 2080,
   opAt 2496 (.Dup ⟨1, by decide⟩),
   opAt 2497 .GT,
   pushAt 2498 2 3158,
   opAt 2499 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2500 .POP,
   opAt 2501 .POP,
   opAt 2502 .POP,
   pushAt 2503 2 2080,
   opAt 2504 .MLOAD,
   opAt 2505 (.Dup ⟨1, by decide⟩),
   opAt 2506 .ADD,
   opAt 2507 (.Dup ⟨0, by decide⟩),
   opAt 2508 (.Swap ⟨1, by decide⟩),
   opAt 2509 .GT,
   opAt 2510 (.Dup ⟨1, by decide⟩),
   opAt 2511 (.Dup ⟨3, by decide⟩),
   opAt 2512 .GT,
   opAt 2513 .GT,
   opAt 2514 (.Swap ⟨1, by decide⟩),
   opAt 2515 (.Swap ⟨0, by decide⟩),
   opAt 2516 .SUB,
   opAt 2517 (.Dup ⟨0, by decide⟩),
   pushAt 2518 2 2080,
   opAt 2519 .MSTORE,
   opAt 2520 (.Dup ⟨1, by decide⟩),
   opAt 2521 .OR,
   pushAt 2522 2 3366,
   opAt 2523 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2531 .JUMPDEST,
   opAt 2532 .ISZERO,
   pushAt 2533 2 3451,
   opAt 2534 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2535 .JUMPDEST,
   pushAt 2536 0 0,
   pushAt 2537 2 2784,
   opAt 2538 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2539 .JUMPDEST,
   opAt 2540 (.Dup ⟨0, by decide⟩),
   opAt 2541 .MLOAD,
   opAt 2542 (.Dup ⟨1, by decide⟩),
   pushAt 2543 2 2112,
   opAt 2544 (.Swap ⟨0, by decide⟩),
   opAt 2545 .SUB,
   opAt 2546 .MLOAD,
   opAt 2547 (.Dup ⟨1, by decide⟩),
   opAt 2548 .ADD,
   opAt 2549 (.Dup ⟨0, by decide⟩),
   opAt 2550 (.Dup ⟨2, by decide⟩),
   opAt 2551 .GT,
   opAt 2552 (.Swap ⟨1, by decide⟩),
   opAt 2553 .POP,
   opAt 2554 (.Dup ⟨3, by decide⟩),
   opAt 2555 .ADD,
   opAt 2556 (.Dup ⟨0, by decide⟩),
   opAt 2557 (.Dup ⟨4, by decide⟩),
   opAt 2558 .GT,
   opAt 2559 (.Swap ⟨3, by decide⟩),
   opAt 2560 .POP,
   opAt 2561 (.Dup ⟨2, by decide⟩),
   opAt 2562 .MSTORE,
   opAt 2563 (.Swap ⟨0, by decide⟩),
   opAt 2564 (.Swap ⟨1, by decide⟩),
   opAt 2565 .OR,
   opAt 2566 (.Swap ⟨0, by decide⟩),
   pushAt 2567 1 31,
   opAt 2568 .NOT,
   opAt 2569 .ADD,
   pushAt 2570 2 2111,
   opAt 2571 (.Dup ⟨1, by decide⟩),
   opAt 2572 .GT,
   pushAt 2573 2 3378,
   opAt 2574 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2575 .POP,
   pushAt 2576 2 2080,
   opAt 2577 .MLOAD,
   opAt 2578 (.Dup ⟨1, by decide⟩),
   opAt 2579 .ADD,
   opAt 2580 (.Dup ⟨0, by decide⟩),
   pushAt 2581 2 2080,
   opAt 2582 .MSTORE,
   opAt 2583 .LT,
   opAt 2584 .ISZERO,
   pushAt 2585 2 3372,
   opAt 2586 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2587 .JUMPDEST,
   pushAt 2588 2 2080,
   opAt 2589 .MLOAD,
   opAt 2590 (.Dup ⟨0, by decide⟩),
   opAt 2591 .ISZERO,
   pushAt 2592 2 3353,
   opAt 2593 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2587 .JUMPDEST,
   pushAt 2588 2 2080,
   opAt 2589 .MLOAD,
   opAt 2590 (.Dup ⟨0, by decide⟩),
   opAt 2591 .ISZERO,
   pushAt 2592 2 3353,
   opAt 2593 .JUMPI,
   opAt 2594 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2595 .JUMPDEST,
   pushAt 2596 0 0,
   pushAt 2597 2 2784,
   opAt 2598 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2599 .JUMPDEST,
   opAt 2600 (.Dup ⟨0, by decide⟩),
   opAt 2601 .MLOAD,
   pushAt 2602 2 2112,
   opAt 2603 (.Dup ⟨2, by decide⟩),
   opAt 2604 .SUB,
   opAt 2605 .MLOAD,
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .GT,
   opAt 2609 (.Swap ⟨1, by decide⟩),
   opAt 2610 .SUB,
   opAt 2611 (.Dup ⟨3, by decide⟩),
   opAt 2612 (.Dup ⟨1, by decide⟩),
   opAt 2613 .LT,
   opAt 2614 (.Swap ⟨0, by decide⟩),
   opAt 2615 (.Dup ⟨4, by decide⟩),
   opAt 2616 (.Swap ⟨0, by decide⟩),
   opAt 2617 .SUB,
   opAt 2618 (.Dup ⟨3, by decide⟩),
   opAt 2619 .MSTORE,
   opAt 2620 .OR,
   opAt 2621 (.Swap ⟨1, by decide⟩),
   opAt 2622 .POP,
   pushAt 2623 1 31,
   opAt 2624 .NOT,
   opAt 2625 .ADD,
   pushAt 2626 2 2111,
   opAt 2627 (.Dup ⟨1, by decide⟩),
   opAt 2628 .GT,
   pushAt 2629 2 3457,
   opAt 2630 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2631 .POP,
   pushAt 2632 2 2080,
   opAt 2633 .MLOAD,
   opAt 2634 .SUB,
   pushAt 2635 2 2080,
   opAt 2636 .MSTORE,
   pushAt 2637 2 3439,
   opAt 2638 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2524 .JUMPDEST,
   opAt 2525 .NOT,
   opAt 2526 .ADD,
   pushAt 2527 2 3039,
   pushAt 2528 2 512,
   pushAt 2529 2 4349,
   opAt 2530 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2659 2 2688,
   opAt 2660 .MLOAD,
   pushAt 2661 2 1280,
   pushAt 2662 2 1024,
   opAt 2663 .MCOPY,
   pushAt 2664 2 2642,
   opAt 2665 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2800 = true :=
  Artifact.isValidJumpDest_index 2091 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2844 = true :=
  Artifact.isValidJumpDest_index 2118 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2861 = true :=
  Artifact.isValidJumpDest_index 2126 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2868 = true :=
  Artifact.isValidJumpDest_index 2130 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2894 = true :=
  Artifact.isValidJumpDest_index 2151 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3039 = true :=
  Artifact.isValidJumpDest_index 2264 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3158 = true :=
  Artifact.isValidJumpDest_index 2347 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3372 = true :=
  Artifact.isValidJumpDest_index 2535 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3378 = true :=
  Artifact.isValidJumpDest_index 2539 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3439 = true :=
  Artifact.isValidJumpDest_index 2587 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3457 = true :=
  Artifact.isValidJumpDest_index 2599 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3366 = true :=
  Artifact.isValidJumpDest_index 2531 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3451 = true :=
  Artifact.isValidJumpDest_index 2595 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3353 = true :=
  Artifact.isValidJumpDest_index 2524 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3510 = true :=
  Artifact.isValidJumpDest_index 2639 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
