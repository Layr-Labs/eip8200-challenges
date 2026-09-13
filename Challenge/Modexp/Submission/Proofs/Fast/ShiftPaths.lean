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
  [opAt 2088 .JUMPDEST,
   opAt 2089 (.Dup ⟨0, by decide⟩),
   opAt 2090 (.Dup ⟨3, by decide⟩),
   opAt 2091 .EQ,
   pushAt 2092 0 0,
   opAt 2093 .MLOAD,
   pushAt 2094 1 255,
   opAt 2095 .SHR,
   opAt 2096 .AND,
   opAt 2097 .ISZERO,
   pushAt 2098 2 2839,
   opAt 2099 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2100 (.Dup ⟨0, by decide⟩),
   pushAt 2101 1 96,
   pushAt 2102 2 256,
   opAt 2103 .CALLDATACOPY,
   opAt 2104 (.Dup ⟨0, by decide⟩),
   pushAt 2105 1 96,
   pushAt 2106 2 2112,
   opAt 2107 .CALLDATACOPY,
   pushAt 2108 0 0,
   pushAt 2109 2 2080,
   opAt 2110 .MSTORE,
   pushAt 2111 2 2856,
   pushAt 2112 2 512,
   pushAt 2113 2 4336,
   opAt 2114 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2115 .JUMPDEST,
   pushAt 2116 1 1,
   pushAt 2117 2 1024,
   opAt 2118 .MSTORE,
   pushAt 2119 2 881,
   pushAt 2120 2 1024,
   pushAt 2121 2 1658,
   opAt 2122 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2123 .JUMPDEST,
   pushAt 2124 1 1,
   pushAt 2125 2 2752,
   opAt 2126 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2148 .POP,
   opAt 2149 .POP,
   pushAt 2150 0 0,
   opAt 2151 .MLOAD,
   opAt 2152 (.Dup ⟨0, by decide⟩),
   pushAt 2153 0 0,
   opAt 2154 .SUB,
   opAt 2155 (.Dup ⟨1, by decide⟩),
   opAt 2156 .AND,
   opAt 2157 (.Dup ⟨0, by decide⟩),
   pushAt 2158 2 1536,
   opAt 2159 .MSTORE,
   opAt 2160 (.Dup ⟨0, by decide⟩),
   opAt 2161 (.Dup ⟨2, by decide⟩),
   opAt 2162 .DIV,
   opAt 2163 (.Dup ⟨0, by decide⟩),
   pushAt 2164 2 1568,
   opAt 2165 .MSTORE,
   opAt 2166 (.Dup ⟨1, by decide⟩),
   opAt 2167 (.Dup ⟨0, by decide⟩),
   pushAt 2168 0 0,
   opAt 2169 .SUB,
   opAt 2170 .DIV,
   pushAt 2171 1 1,
   opAt 2172 .ADD,
   pushAt 2173 2 1600,
   opAt 2174 .MSTORE,
   opAt 2175 (.Dup ⟨0, by decide⟩),
   opAt 2176 (.Dup ⟨0, by decide⟩),
   pushAt 2177 0 0,
   opAt 2178 .SUB,
   opAt 2179 .MOD,
   pushAt 2180 2 1632,
   opAt 2181 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2182 (.Dup ⟨0, by decide⟩),
   pushAt 2183 1 3,
   opAt 2184 .MUL,
   pushAt 2185 1 2,
   opAt 2186 .XOR,
   opAt 2187 (.Dup ⟨0, by decide⟩),
   opAt 2188 (.Dup ⟨2, by decide⟩),
   opAt 2189 .MUL,
   pushAt 2190 1 2,
   opAt 2191 .SUB,
   opAt 2192 .MUL,
   opAt 2193 (.Dup ⟨0, by decide⟩),
   opAt 2194 (.Dup ⟨2, by decide⟩),
   opAt 2195 .MUL,
   pushAt 2196 1 2,
   opAt 2197 .SUB,
   opAt 2198 .MUL,
   opAt 2199 (.Dup ⟨0, by decide⟩),
   opAt 2200 (.Dup ⟨2, by decide⟩),
   opAt 2201 .MUL,
   pushAt 2202 1 2,
   opAt 2203 .SUB,
   opAt 2204 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2205 (.Dup ⟨0, by decide⟩),
   opAt 2206 (.Dup ⟨2, by decide⟩),
   opAt 2207 .MUL,
   pushAt 2208 1 2,
   opAt 2209 .SUB,
   opAt 2210 .MUL,
   opAt 2211 (.Dup ⟨0, by decide⟩),
   opAt 2212 (.Dup ⟨2, by decide⟩),
   opAt 2213 .MUL,
   pushAt 2214 1 2,
   opAt 2215 .SUB,
   opAt 2216 .MUL,
   opAt 2217 (.Dup ⟨0, by decide⟩),
   opAt 2218 (.Dup ⟨2, by decide⟩),
   opAt 2219 .MUL,
   pushAt 2220 1 2,
   opAt 2221 .SUB,
   opAt 2222 .MUL,
   pushAt 2223 2 1664,
   opAt 2224 .MSTORE,
   opAt 2225 .POP,
   opAt 2226 .POP,
   opAt 2227 .POP,
   opAt 2228 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2260 .JUMPDEST,
   opAt 2261 (.Dup ⟨0, by decide⟩),
   opAt 2262 .ISZERO,
   pushAt 2263 2 3502,
   opAt 2264 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2265 (.Dup ⟨1, by decide⟩),
   pushAt 2266 2 512,
   pushAt 2267 2 2080,
   opAt 2268 .MCOPY,
   pushAt 2269 0 0,
   pushAt 2270 2 2784,
   opAt 2271 .MLOAD,
   opAt 2272 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2273 2 512,
   opAt 2274 .MLOAD,
   pushAt 2275 2 1536,
   opAt 2276 .MLOAD,
   opAt 2277 (.Dup ⟨1, by decide⟩),
   opAt 2278 .DIV,
   opAt 2279 (.Swap ⟨0, by decide⟩),
   pushAt 2280 2 1600,
   opAt 2281 .MLOAD,
   opAt 2282 .MUL,
   pushAt 2283 2 544,
   opAt 2284 .MLOAD,
   pushAt 2285 2 1536,
   opAt 2286 .MLOAD,
   opAt 2287 (.Swap ⟨0, by decide⟩),
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
   pushAt 2333 2 2784,
   opAt 2334 .MLOAD,
   pushAt 2335 0 0,
   opAt 2336 .NOT,
   opAt 2337 (.Swap ⟨0, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2341 .JUMPDEST,
   pushAt 2342 2 832,
   opAt 2343 (.Dup ⟨1, by decide⟩),
   opAt 2344 .SUB,
   opAt 2345 .MLOAD,
   opAt 2346 (.Dup ⟨2, by decide⟩),
   opAt 2347 (.Dup ⟨6, by decide⟩),
   opAt 2348 (.Dup ⟨2, by decide⟩),
   opAt 2349 .MUL,
   opAt 2350 (.Swap ⟨1, by decide⟩),
   opAt 2351 (.Dup ⟨7, by decide⟩),
   opAt 2352 .MULMOD,
   opAt 2353 (.Dup ⟨1, by decide⟩),
   opAt 2354 (.Dup ⟨1, by decide⟩),
   opAt 2355 .LT,
   opAt 2356 .SUB,
   opAt 2357 (.Dup ⟨5, by decide⟩),
   opAt 2358 (.Dup ⟨2, by decide⟩),
   opAt 2359 .ADD,
   opAt 2360 (.Dup ⟨0, by decide⟩),
   opAt 2361 (.Swap ⟨6, by decide⟩),
   opAt 2362 .GT,
   opAt 2363 .SUB,
   opAt 2364 .SUB,
   opAt 2365 (.Dup ⟨4, by decide⟩),
   opAt 2366 (.Dup ⟨2, by decide⟩),
   opAt 2367 .MLOAD,
   opAt 2368 .ADD,
   opAt 2369 (.Dup ⟨0, by decide⟩),
   opAt 2370 (.Swap ⟨5, by decide⟩),
   opAt 2371 .GT,
   opAt 2372 .ADD,
   opAt 2373 (.Swap ⟨3, by decide⟩),
   opAt 2374 (.Dup ⟨1, by decide⟩),
   opAt 2375 .MSTORE,
   opAt 2376 (.Dup ⟨2, by decide⟩),
   opAt 2377 .ADD,
   pushAt 2489 2 2080,
   opAt 2490 (.Dup ⟨1, by decide⟩),
   opAt 2491 .GT,
   pushAt 2492 2 3150,
   opAt 2493 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2494 .POP,
   opAt 2495 .POP,
   opAt 2496 .POP,
   pushAt 2497 2 2080,
   opAt 2498 .MLOAD,
   opAt 2499 (.Dup ⟨1, by decide⟩),
   opAt 2500 .ADD,
   opAt 2501 (.Dup ⟨0, by decide⟩),
   opAt 2502 (.Swap ⟨1, by decide⟩),
   opAt 2503 .GT,
   opAt 2504 (.Dup ⟨1, by decide⟩),
   opAt 2505 (.Dup ⟨3, by decide⟩),
   opAt 2506 .GT,
   opAt 2507 .GT,
   opAt 2508 (.Swap ⟨1, by decide⟩),
   opAt 2509 (.Swap ⟨0, by decide⟩),
   opAt 2510 .SUB,
   opAt 2511 (.Dup ⟨0, by decide⟩),
   pushAt 2512 2 2080,
   opAt 2513 .MSTORE,
   opAt 2514 (.Dup ⟨1, by decide⟩),
   opAt 2515 .OR,
   pushAt 2516 2 3358,
   opAt 2517 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2525 .JUMPDEST,
   opAt 2526 .ISZERO,
   pushAt 2527 2 3443,
   opAt 2528 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2529 .JUMPDEST,
   pushAt 2530 0 0,
   pushAt 2531 2 2784,
   opAt 2532 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2533 .JUMPDEST,
   opAt 2534 (.Dup ⟨0, by decide⟩),
   opAt 2535 .MLOAD,
   opAt 2536 (.Dup ⟨1, by decide⟩),
   pushAt 2537 2 2112,
   opAt 2538 (.Swap ⟨0, by decide⟩),
   opAt 2539 .SUB,
   opAt 2540 .MLOAD,
   opAt 2541 (.Dup ⟨1, by decide⟩),
   opAt 2542 .ADD,
   opAt 2543 (.Dup ⟨0, by decide⟩),
   opAt 2544 (.Dup ⟨2, by decide⟩),
   opAt 2545 .GT,
   opAt 2546 (.Swap ⟨1, by decide⟩),
   opAt 2547 .POP,
   opAt 2548 (.Dup ⟨3, by decide⟩),
   opAt 2549 .ADD,
   opAt 2550 (.Dup ⟨0, by decide⟩),
   opAt 2551 (.Dup ⟨4, by decide⟩),
   opAt 2552 .GT,
   opAt 2553 (.Swap ⟨3, by decide⟩),
   opAt 2554 .POP,
   opAt 2555 (.Dup ⟨2, by decide⟩),
   opAt 2556 .MSTORE,
   opAt 2557 (.Swap ⟨0, by decide⟩),
   opAt 2558 (.Swap ⟨1, by decide⟩),
   opAt 2559 .OR,
   opAt 2560 (.Swap ⟨0, by decide⟩),
   pushAt 2561 1 31,
   opAt 2562 .NOT,
   opAt 2563 .ADD,
   pushAt 2564 2 2111,
   opAt 2565 (.Dup ⟨1, by decide⟩),
   opAt 2566 .GT,
   pushAt 2567 2 3370,
   opAt 2568 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2569 .POP,
   pushAt 2570 2 2080,
   opAt 2571 .MLOAD,
   opAt 2572 (.Dup ⟨1, by decide⟩),
   opAt 2573 .ADD,
   opAt 2574 (.Dup ⟨0, by decide⟩),
   pushAt 2575 2 2080,
   opAt 2576 .MSTORE,
   opAt 2577 .LT,
   opAt 2578 .ISZERO,
   pushAt 2579 2 3364,
   opAt 2580 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2581 .JUMPDEST,
   pushAt 2582 2 2080,
   opAt 2583 .MLOAD,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   opAt 2585 .ISZERO,
   pushAt 2586 2 3345,
   opAt 2587 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2581 .JUMPDEST,
   pushAt 2582 2 2080,
   opAt 2583 .MLOAD,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   opAt 2585 .ISZERO,
   pushAt 2586 2 3345,
   opAt 2587 .JUMPI,
   opAt 2588 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2589 .JUMPDEST,
   pushAt 2590 0 0,
   pushAt 2591 2 2784,
   opAt 2592 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2593 .JUMPDEST,
   opAt 2594 (.Dup ⟨0, by decide⟩),
   opAt 2595 .MLOAD,
   pushAt 2596 2 2112,
   opAt 2597 (.Dup ⟨2, by decide⟩),
   opAt 2598 .SUB,
   opAt 2599 .MLOAD,
   opAt 2600 (.Dup ⟨1, by decide⟩),
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 .GT,
   opAt 2603 (.Swap ⟨1, by decide⟩),
   opAt 2604 .SUB,
   opAt 2605 (.Dup ⟨3, by decide⟩),
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 .LT,
   opAt 2608 (.Swap ⟨0, by decide⟩),
   opAt 2609 (.Dup ⟨4, by decide⟩),
   opAt 2610 (.Swap ⟨0, by decide⟩),
   opAt 2611 .SUB,
   opAt 2612 (.Dup ⟨3, by decide⟩),
   opAt 2613 .MSTORE,
   opAt 2614 .OR,
   opAt 2615 (.Swap ⟨1, by decide⟩),
   opAt 2616 .POP,
   pushAt 2617 1 31,
   opAt 2618 .NOT,
   opAt 2619 .ADD,
   pushAt 2620 2 2111,
   opAt 2621 (.Dup ⟨1, by decide⟩),
   opAt 2622 .GT,
   pushAt 2623 2 3449,
   opAt 2624 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2625 .POP,
   pushAt 2626 2 2080,
   opAt 2627 .MLOAD,
   opAt 2628 .SUB,
   pushAt 2629 2 2080,
   opAt 2630 .MSTORE,
   pushAt 2631 2 3431,
   opAt 2632 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2518 .JUMPDEST,
   opAt 2519 .NOT,
   opAt 2520 .ADD,
   pushAt 2521 2 3033,
   pushAt 2522 2 512,
   pushAt 2523 2 4336,
   opAt 2524 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2653 2 2688,
   opAt 2654 .MLOAD,
   pushAt 2655 2 1280,
   pushAt 2656 2 1024,
   opAt 2657 .MCOPY,
   pushAt 2658 2 2638,
   opAt 2659 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2795 = true :=
  Artifact.isValidJumpDest_index 2088 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2839 = true :=
  Artifact.isValidJumpDest_index 2115 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2856 = true :=
  Artifact.isValidJumpDest_index 2123 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2863 = true :=
  Artifact.isValidJumpDest_index 2127 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3033 = true :=
  Artifact.isValidJumpDest_index 2260 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3150 = true :=
  Artifact.isValidJumpDest_index 2341 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3364 = true :=
  Artifact.isValidJumpDest_index 2529 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3370 = true :=
  Artifact.isValidJumpDest_index 2533 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3431 = true :=
  Artifact.isValidJumpDest_index 2581 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3449 = true :=
  Artifact.isValidJumpDest_index 2593 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3358 = true :=
  Artifact.isValidJumpDest_index 2525 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3443 = true :=
  Artifact.isValidJumpDest_index 2589 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3345 = true :=
  Artifact.isValidJumpDest_index 2518 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3502 = true :=
  Artifact.isValidJumpDest_index 2633 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
