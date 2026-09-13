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
   pushAt 2116 2 4347,
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
   pushAt 2267 2 3508,
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
   pushAt 2284 2 1600,
   opAt 2285 .MLOAD,
   opAt 2286 .MUL,
   pushAt 2287 2 544,
   opAt 2288 .MLOAD,
   pushAt 2289 2 1536,
   opAt 2290 .MLOAD,
   opAt 2291 (.Swap ⟨0, by decide⟩),
   opAt 2292 .DIV,
   opAt 2293 .ADD,
   pushAt 2294 2 1568,
   opAt 2295 .MLOAD,
   opAt 2296 (.Dup ⟨0, by decide⟩),
   pushAt 2297 2 1632,
   opAt 2298 .MLOAD,
   opAt 2299 (.Dup ⟨4, by decide⟩),
   opAt 2300 .MULMOD,
   opAt 2301 (.Dup ⟨2, by decide⟩),
   opAt 2302 .ADDMOD,
   opAt 2303 (.Swap ⟨0, by decide⟩),
   opAt 2304 .SUB,
   pushAt 2305 2 1664,
   opAt 2306 .MLOAD,
   opAt 2307 .MUL,
   opAt 2308 (.Dup ⟨0, by decide⟩),
   pushAt 2309 0 0,
   opAt 2310 .MLOAD,
   opAt 2311 .MUL,
   pushAt 2312 2 544,
   opAt 2313 .MLOAD,
   opAt 2314 .SUB,
   pushAt 2315 1 32,
   opAt 2316 .MLOAD,
   pushAt 2317 1 128,
   opAt 2318 .SHR,
   opAt 2319 (.Dup ⟨2, by decide⟩),
   pushAt 2320 1 128,
   opAt 2321 .SHR,
   opAt 2322 .MUL,
   opAt 2323 .GT,
   opAt 2324 (.Swap ⟨0, by decide⟩),
   opAt 2325 .SUB,
   opAt 2326 (.Swap ⟨0, by decide⟩),
   pushAt 2327 2 1568,
   opAt 2328 .MLOAD,
   opAt 2329 .GT,
   opAt 2330 .ISZERO,
   pushAt 2331 0 0,
   opAt 2332 .SUB,
   opAt 2333 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2334 0 0,
   pushAt 2335 1 31,
   opAt 2336 .NOT,
   pushAt 2337 2 2784,
   opAt 2338 .MLOAD,
   pushAt 2339 0 0,
   opAt 2340 .NOT,
   opAt 2341 (.Swap ⟨0, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2345 .JUMPDEST,
   pushAt 2346 2 832,
   opAt 2347 (.Dup ⟨1, by decide⟩),
   opAt 2348 .SUB,
   opAt 2349 .MLOAD,
   opAt 2350 (.Dup ⟨2, by decide⟩),
   opAt 2351 (.Dup ⟨6, by decide⟩),
   opAt 2352 (.Dup ⟨2, by decide⟩),
   opAt 2353 .MUL,
   opAt 2354 (.Swap ⟨1, by decide⟩),
   opAt 2355 (.Dup ⟨7, by decide⟩),
   opAt 2356 .MULMOD,
   opAt 2357 (.Dup ⟨1, by decide⟩),
   opAt 2358 (.Dup ⟨1, by decide⟩),
   opAt 2359 .LT,
   opAt 2360 .SUB,
   opAt 2361 (.Dup ⟨5, by decide⟩),
   opAt 2362 (.Dup ⟨2, by decide⟩),
   opAt 2363 .ADD,
   opAt 2364 (.Dup ⟨0, by decide⟩),
   opAt 2365 (.Swap ⟨6, by decide⟩),
   opAt 2366 .GT,
   opAt 2367 .SUB,
   opAt 2368 .SUB,
   opAt 2369 (.Dup ⟨4, by decide⟩),
   opAt 2370 (.Dup ⟨2, by decide⟩),
   opAt 2371 .MLOAD,
   opAt 2372 .ADD,
   opAt 2373 (.Dup ⟨0, by decide⟩),
   opAt 2374 (.Swap ⟨5, by decide⟩),
   opAt 2375 .GT,
   opAt 2376 .ADD,
   opAt 2377 (.Swap ⟨3, by decide⟩),
   opAt 2378 (.Dup ⟨1, by decide⟩),
   opAt 2379 .MSTORE,
   opAt 2380 (.Dup ⟨2, by decide⟩),
   opAt 2381 .ADD,
   pushAt 2493 2 2080,
   opAt 2494 (.Dup ⟨1, by decide⟩),
   opAt 2495 .GT,
   pushAt 2496 2 3156,
   opAt 2497 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2498 .POP,
   opAt 2499 .POP,
   opAt 2500 .POP,
   pushAt 2501 2 2080,
   opAt 2502 .MLOAD,
   opAt 2503 (.Dup ⟨1, by decide⟩),
   opAt 2504 .ADD,
   opAt 2505 (.Dup ⟨0, by decide⟩),
   opAt 2506 (.Swap ⟨1, by decide⟩),
   opAt 2507 .GT,
   opAt 2508 (.Dup ⟨1, by decide⟩),
   opAt 2509 (.Dup ⟨3, by decide⟩),
   opAt 2510 .GT,
   opAt 2511 .GT,
   opAt 2512 (.Swap ⟨1, by decide⟩),
   opAt 2513 (.Swap ⟨0, by decide⟩),
   opAt 2514 .SUB,
   opAt 2515 (.Dup ⟨0, by decide⟩),
   pushAt 2516 2 2080,
   opAt 2517 .MSTORE,
   opAt 2518 (.Dup ⟨1, by decide⟩),
   opAt 2519 .OR,
   pushAt 2520 2 3364,
   opAt 2521 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2529 .JUMPDEST,
   opAt 2530 .ISZERO,
   pushAt 2531 2 3449,
   opAt 2532 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2533 .JUMPDEST,
   pushAt 2534 0 0,
   pushAt 2535 2 2784,
   opAt 2536 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2537 .JUMPDEST,
   opAt 2538 (.Dup ⟨0, by decide⟩),
   opAt 2539 .MLOAD,
   opAt 2540 (.Dup ⟨1, by decide⟩),
   pushAt 2541 2 2112,
   opAt 2542 (.Swap ⟨0, by decide⟩),
   opAt 2543 .SUB,
   opAt 2544 .MLOAD,
   opAt 2545 (.Dup ⟨1, by decide⟩),
   opAt 2546 .ADD,
   opAt 2547 (.Dup ⟨0, by decide⟩),
   opAt 2548 (.Dup ⟨2, by decide⟩),
   opAt 2549 .GT,
   opAt 2550 (.Swap ⟨1, by decide⟩),
   opAt 2551 .POP,
   opAt 2552 (.Dup ⟨3, by decide⟩),
   opAt 2553 .ADD,
   opAt 2554 (.Dup ⟨0, by decide⟩),
   opAt 2555 (.Dup ⟨4, by decide⟩),
   opAt 2556 .GT,
   opAt 2557 (.Swap ⟨3, by decide⟩),
   opAt 2558 .POP,
   opAt 2559 (.Dup ⟨2, by decide⟩),
   opAt 2560 .MSTORE,
   opAt 2561 (.Swap ⟨0, by decide⟩),
   opAt 2562 (.Swap ⟨1, by decide⟩),
   opAt 2563 .OR,
   opAt 2564 (.Swap ⟨0, by decide⟩),
   pushAt 2565 1 31,
   opAt 2566 .NOT,
   opAt 2567 .ADD,
   pushAt 2568 2 2111,
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .GT,
   pushAt 2571 2 3376,
   opAt 2572 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2573 .POP,
   pushAt 2574 2 2080,
   opAt 2575 .MLOAD,
   opAt 2576 (.Dup ⟨1, by decide⟩),
   opAt 2577 .ADD,
   opAt 2578 (.Dup ⟨0, by decide⟩),
   pushAt 2579 2 2080,
   opAt 2580 .MSTORE,
   opAt 2581 .LT,
   opAt 2582 .ISZERO,
   pushAt 2583 2 3370,
   opAt 2584 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2585 .JUMPDEST,
   pushAt 2586 2 2080,
   opAt 2587 .MLOAD,
   opAt 2588 (.Dup ⟨0, by decide⟩),
   opAt 2589 .ISZERO,
   pushAt 2590 2 3351,
   opAt 2591 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2585 .JUMPDEST,
   pushAt 2586 2 2080,
   opAt 2587 .MLOAD,
   opAt 2588 (.Dup ⟨0, by decide⟩),
   opAt 2589 .ISZERO,
   pushAt 2590 2 3351,
   opAt 2591 .JUMPI,
   opAt 2592 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2593 .JUMPDEST,
   pushAt 2594 0 0,
   pushAt 2595 2 2784,
   opAt 2596 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2597 .JUMPDEST,
   opAt 2598 (.Dup ⟨0, by decide⟩),
   opAt 2599 .MLOAD,
   pushAt 2600 2 2112,
   opAt 2601 (.Dup ⟨2, by decide⟩),
   opAt 2602 .SUB,
   opAt 2603 .MLOAD,
   opAt 2604 (.Dup ⟨1, by decide⟩),
   opAt 2605 (.Dup ⟨1, by decide⟩),
   opAt 2606 .GT,
   opAt 2607 (.Swap ⟨1, by decide⟩),
   opAt 2608 .SUB,
   opAt 2609 (.Dup ⟨3, by decide⟩),
   opAt 2610 (.Dup ⟨1, by decide⟩),
   opAt 2611 .LT,
   opAt 2612 (.Swap ⟨0, by decide⟩),
   opAt 2613 (.Dup ⟨4, by decide⟩),
   opAt 2614 (.Swap ⟨0, by decide⟩),
   opAt 2615 .SUB,
   opAt 2616 (.Dup ⟨3, by decide⟩),
   opAt 2617 .MSTORE,
   opAt 2618 .OR,
   opAt 2619 (.Swap ⟨1, by decide⟩),
   opAt 2620 .POP,
   pushAt 2621 1 31,
   opAt 2622 .NOT,
   opAt 2623 .ADD,
   pushAt 2624 2 2111,
   opAt 2625 (.Dup ⟨1, by decide⟩),
   opAt 2626 .GT,
   pushAt 2627 2 3455,
   opAt 2628 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2629 .POP,
   pushAt 2630 2 2080,
   opAt 2631 .MLOAD,
   opAt 2632 .SUB,
   pushAt 2633 2 2080,
   opAt 2634 .MSTORE,
   pushAt 2635 2 3437,
   opAt 2636 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2522 .JUMPDEST,
   opAt 2523 .NOT,
   opAt 2524 .ADD,
   pushAt 2525 2 3039,
   pushAt 2526 2 512,
   pushAt 2527 2 4347,
   opAt 2528 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2657 2 2688,
   opAt 2658 .MLOAD,
   pushAt 2659 2 1280,
   pushAt 2660 2 1024,
   opAt 2661 .MCOPY,
   pushAt 2662 2 2642,
   opAt 2663 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2345 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3370 = true :=
  Artifact.isValidJumpDest_index 2533 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3376 = true :=
  Artifact.isValidJumpDest_index 2537 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3437 = true :=
  Artifact.isValidJumpDest_index 2585 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3455 = true :=
  Artifact.isValidJumpDest_index 2597 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3364 = true :=
  Artifact.isValidJumpDest_index 2529 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3449 = true :=
  Artifact.isValidJumpDest_index 2593 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3351 = true :=
  Artifact.isValidJumpDest_index 2522 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3508 = true :=
  Artifact.isValidJumpDest_index 2637 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
