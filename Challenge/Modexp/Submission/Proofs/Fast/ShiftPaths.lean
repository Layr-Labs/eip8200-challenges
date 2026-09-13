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
   pushAt 2113 2 4338,
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
   pushAt 2263 2 3504,
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
   opAt 2280 .JUMPDEST,
   opAt 2281 .JUMPDEST,
   pushAt 2282 2 1600,
   opAt 2283 .MLOAD,
   opAt 2284 .MUL,
   pushAt 2285 2 544,
   opAt 2286 .MLOAD,
   pushAt 2287 2 1536,
   opAt 2288 .MLOAD,
   opAt 2289 (.Swap ⟨0, by decide⟩),
   opAt 2290 .DIV,
   opAt 2291 .ADD,
   pushAt 2292 2 1568,
   opAt 2293 .MLOAD,
   opAt 2294 (.Dup ⟨0, by decide⟩),
   pushAt 2295 2 1632,
   opAt 2296 .MLOAD,
   opAt 2297 (.Dup ⟨4, by decide⟩),
   opAt 2298 .MULMOD,
   opAt 2299 (.Dup ⟨2, by decide⟩),
   opAt 2300 .ADDMOD,
   opAt 2301 (.Swap ⟨0, by decide⟩),
   opAt 2302 .SUB,
   pushAt 2303 2 1664,
   opAt 2304 .MLOAD,
   opAt 2305 .MUL,
   opAt 2306 (.Dup ⟨0, by decide⟩),
   pushAt 2307 0 0,
   opAt 2308 .MLOAD,
   opAt 2309 .MUL,
   pushAt 2310 2 544,
   opAt 2311 .MLOAD,
   opAt 2312 .SUB,
   pushAt 2313 1 32,
   opAt 2314 .MLOAD,
   pushAt 2315 1 128,
   opAt 2316 .SHR,
   opAt 2317 (.Dup ⟨2, by decide⟩),
   pushAt 2318 1 128,
   opAt 2319 .SHR,
   opAt 2320 .MUL,
   opAt 2321 .GT,
   opAt 2322 (.Swap ⟨0, by decide⟩),
   opAt 2323 .SUB,
   opAt 2324 (.Swap ⟨0, by decide⟩),
   pushAt 2325 2 1568,
   opAt 2326 .MLOAD,
   opAt 2327 .GT,
   opAt 2328 .ISZERO,
   pushAt 2329 0 0,
   opAt 2330 .SUB,
   opAt 2331 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2332 0 0,
   pushAt 2333 1 31,
   opAt 2334 .NOT,
   pushAt 2335 2 2784,
   opAt 2336 .MLOAD,
   pushAt 2337 0 0,
   opAt 2338 .NOT,
   opAt 2339 (.Swap ⟨0, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2343 .JUMPDEST,
   pushAt 2344 2 832,
   opAt 2345 (.Dup ⟨1, by decide⟩),
   opAt 2346 .SUB,
   opAt 2347 .MLOAD,
   opAt 2348 (.Dup ⟨2, by decide⟩),
   opAt 2349 (.Dup ⟨6, by decide⟩),
   opAt 2350 (.Dup ⟨2, by decide⟩),
   opAt 2351 .MUL,
   opAt 2352 (.Swap ⟨1, by decide⟩),
   opAt 2353 (.Dup ⟨7, by decide⟩),
   opAt 2354 .MULMOD,
   opAt 2355 (.Dup ⟨1, by decide⟩),
   opAt 2356 (.Dup ⟨1, by decide⟩),
   opAt 2357 .LT,
   opAt 2358 .SUB,
   opAt 2359 (.Dup ⟨5, by decide⟩),
   opAt 2360 (.Dup ⟨2, by decide⟩),
   opAt 2361 .ADD,
   opAt 2362 (.Dup ⟨0, by decide⟩),
   opAt 2363 (.Swap ⟨6, by decide⟩),
   opAt 2364 .GT,
   opAt 2365 .SUB,
   opAt 2366 .SUB,
   opAt 2367 (.Dup ⟨4, by decide⟩),
   opAt 2368 (.Dup ⟨2, by decide⟩),
   opAt 2369 .MLOAD,
   opAt 2370 .ADD,
   opAt 2371 (.Dup ⟨0, by decide⟩),
   opAt 2372 (.Swap ⟨5, by decide⟩),
   opAt 2373 .GT,
   opAt 2374 .ADD,
   opAt 2375 (.Swap ⟨3, by decide⟩),
   opAt 2376 (.Dup ⟨1, by decide⟩),
   opAt 2377 .MSTORE,
   opAt 2378 (.Dup ⟨2, by decide⟩),
   opAt 2379 .ADD,
   pushAt 2491 2 2080,
   opAt 2492 (.Dup ⟨1, by decide⟩),
   opAt 2493 .GT,
   pushAt 2494 2 3152,
   opAt 2495 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2496 .POP,
   opAt 2497 .POP,
   opAt 2498 .POP,
   pushAt 2499 2 2080,
   opAt 2500 .MLOAD,
   opAt 2501 (.Dup ⟨1, by decide⟩),
   opAt 2502 .ADD,
   opAt 2503 (.Dup ⟨0, by decide⟩),
   opAt 2504 (.Swap ⟨1, by decide⟩),
   opAt 2505 .GT,
   opAt 2506 (.Dup ⟨1, by decide⟩),
   opAt 2507 (.Dup ⟨3, by decide⟩),
   opAt 2508 .GT,
   opAt 2509 .GT,
   opAt 2510 (.Swap ⟨1, by decide⟩),
   opAt 2511 (.Swap ⟨0, by decide⟩),
   opAt 2512 .SUB,
   opAt 2513 (.Dup ⟨0, by decide⟩),
   pushAt 2514 2 2080,
   opAt 2515 .MSTORE,
   opAt 2516 (.Dup ⟨1, by decide⟩),
   opAt 2517 .OR,
   pushAt 2518 2 3360,
   opAt 2519 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2527 .JUMPDEST,
   opAt 2528 .ISZERO,
   pushAt 2529 2 3445,
   opAt 2530 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2531 .JUMPDEST,
   pushAt 2532 0 0,
   pushAt 2533 2 2784,
   opAt 2534 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2535 .JUMPDEST,
   opAt 2536 (.Dup ⟨0, by decide⟩),
   opAt 2537 .MLOAD,
   opAt 2538 (.Dup ⟨1, by decide⟩),
   pushAt 2539 2 2112,
   opAt 2540 (.Swap ⟨0, by decide⟩),
   opAt 2541 .SUB,
   opAt 2542 .MLOAD,
   opAt 2543 (.Dup ⟨1, by decide⟩),
   opAt 2544 .ADD,
   opAt 2545 (.Dup ⟨0, by decide⟩),
   opAt 2546 (.Dup ⟨2, by decide⟩),
   opAt 2547 .GT,
   opAt 2548 (.Swap ⟨1, by decide⟩),
   opAt 2549 .POP,
   opAt 2550 (.Dup ⟨3, by decide⟩),
   opAt 2551 .ADD,
   opAt 2552 (.Dup ⟨0, by decide⟩),
   opAt 2553 (.Dup ⟨4, by decide⟩),
   opAt 2554 .GT,
   opAt 2555 (.Swap ⟨3, by decide⟩),
   opAt 2556 .POP,
   opAt 2557 (.Dup ⟨2, by decide⟩),
   opAt 2558 .MSTORE,
   opAt 2559 (.Swap ⟨0, by decide⟩),
   opAt 2560 (.Swap ⟨1, by decide⟩),
   opAt 2561 .OR,
   opAt 2562 (.Swap ⟨0, by decide⟩),
   pushAt 2563 1 31,
   opAt 2564 .NOT,
   opAt 2565 .ADD,
   pushAt 2566 2 2111,
   opAt 2567 (.Dup ⟨1, by decide⟩),
   opAt 2568 .GT,
   pushAt 2569 2 3372,
   opAt 2570 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2571 .POP,
   pushAt 2572 2 2080,
   opAt 2573 .MLOAD,
   opAt 2574 (.Dup ⟨1, by decide⟩),
   opAt 2575 .ADD,
   opAt 2576 (.Dup ⟨0, by decide⟩),
   pushAt 2577 2 2080,
   opAt 2578 .MSTORE,
   opAt 2579 .LT,
   opAt 2580 .ISZERO,
   pushAt 2581 2 3366,
   opAt 2582 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .JUMPDEST,
   pushAt 2584 2 2080,
   opAt 2585 .MLOAD,
   opAt 2586 (.Dup ⟨0, by decide⟩),
   opAt 2587 .ISZERO,
   pushAt 2588 2 3347,
   opAt 2589 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .JUMPDEST,
   pushAt 2584 2 2080,
   opAt 2585 .MLOAD,
   opAt 2586 (.Dup ⟨0, by decide⟩),
   opAt 2587 .ISZERO,
   pushAt 2588 2 3347,
   opAt 2589 .JUMPI,
   opAt 2590 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2591 .JUMPDEST,
   pushAt 2592 0 0,
   pushAt 2593 2 2784,
   opAt 2594 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2595 .JUMPDEST,
   opAt 2596 (.Dup ⟨0, by decide⟩),
   opAt 2597 .MLOAD,
   pushAt 2598 2 2112,
   opAt 2599 (.Dup ⟨2, by decide⟩),
   opAt 2600 .SUB,
   opAt 2601 .MLOAD,
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 (.Dup ⟨1, by decide⟩),
   opAt 2604 .GT,
   opAt 2605 (.Swap ⟨1, by decide⟩),
   opAt 2606 .SUB,
   opAt 2607 (.Dup ⟨3, by decide⟩),
   opAt 2608 (.Dup ⟨1, by decide⟩),
   opAt 2609 .LT,
   opAt 2610 (.Swap ⟨0, by decide⟩),
   opAt 2611 (.Dup ⟨4, by decide⟩),
   opAt 2612 (.Swap ⟨0, by decide⟩),
   opAt 2613 .SUB,
   opAt 2614 (.Dup ⟨3, by decide⟩),
   opAt 2615 .MSTORE,
   opAt 2616 .OR,
   opAt 2617 (.Swap ⟨1, by decide⟩),
   opAt 2618 .POP,
   pushAt 2619 1 31,
   opAt 2620 .NOT,
   opAt 2621 .ADD,
   pushAt 2622 2 2111,
   opAt 2623 (.Dup ⟨1, by decide⟩),
   opAt 2624 .GT,
   pushAt 2625 2 3451,
   opAt 2626 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2627 .POP,
   pushAt 2628 2 2080,
   opAt 2629 .MLOAD,
   opAt 2630 .SUB,
   pushAt 2631 2 2080,
   opAt 2632 .MSTORE,
   pushAt 2633 2 3433,
   opAt 2634 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2520 .JUMPDEST,
   opAt 2521 .NOT,
   opAt 2522 .ADD,
   pushAt 2523 2 3033,
   pushAt 2524 2 512,
   pushAt 2525 2 4338,
   opAt 2526 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2655 2 2688,
   opAt 2656 .MLOAD,
   pushAt 2657 2 1280,
   pushAt 2658 2 1024,
   opAt 2659 .MCOPY,
   pushAt 2660 2 2638,
   opAt 2661 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3152 = true :=
  Artifact.isValidJumpDest_index 2343 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3366 = true :=
  Artifact.isValidJumpDest_index 2531 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3372 = true :=
  Artifact.isValidJumpDest_index 2535 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3433 = true :=
  Artifact.isValidJumpDest_index 2583 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3451 = true :=
  Artifact.isValidJumpDest_index 2595 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3360 = true :=
  Artifact.isValidJumpDest_index 2527 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3445 = true :=
  Artifact.isValidJumpDest_index 2591 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3347 = true :=
  Artifact.isValidJumpDest_index 2520 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3504 = true :=
  Artifact.isValidJumpDest_index 2635 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
