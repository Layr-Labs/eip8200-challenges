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
  [opAt 2086 .JUMPDEST,
   opAt 2087 (.Dup ⟨0, by decide⟩),
   opAt 2088 (.Dup ⟨3, by decide⟩),
   opAt 2089 .EQ,
   pushAt 2090 0 0,
   opAt 2091 .MLOAD,
   pushAt 2092 1 255,
   opAt 2093 .SHR,
   opAt 2094 .AND,
   opAt 2095 .ISZERO,
   pushAt 2096 2 2827,
   opAt 2097 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2098 (.Dup ⟨0, by decide⟩),
   pushAt 2099 1 96,
   pushAt 2100 2 2112,
   opAt 2101 .CALLDATACOPY,
   pushAt 2102 0 0,
   pushAt 2103 2 2080,
   opAt 2104 .MSTORE,
   pushAt 2105 2 2844,
   pushAt 2106 2 4486,
   opAt 2107 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2108 .JUMPDEST,
   pushAt 2109 1 1,
   pushAt 2110 2 1024,
   opAt 2111 .MSTORE,
   pushAt 2112 2 880,
   pushAt 2113 2 1024,
   pushAt 2114 2 1658,
   opAt 2115 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2121 1 1,
   pushAt 2122 2 2752,
   opAt 2123 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2145 .POP,
   opAt 2146 .POP,
   pushAt 2147 0 0,
   opAt 2148 .MLOAD,
   opAt 2149 (.Dup ⟨0, by decide⟩),
   pushAt 2150 0 0,
   opAt 2151 .SUB,
   opAt 2152 (.Dup ⟨1, by decide⟩),
   opAt 2153 .AND,
   opAt 2154 (.Dup ⟨0, by decide⟩),
   pushAt 2155 2 1536,
   opAt 2156 .MSTORE,
   opAt 2157 (.Dup ⟨0, by decide⟩),
   opAt 2158 (.Dup ⟨2, by decide⟩),
   opAt 2159 .DIV,
   opAt 2160 (.Dup ⟨0, by decide⟩),
   pushAt 2161 2 1568,
   opAt 2162 .MSTORE,
   opAt 2163 (.Dup ⟨1, by decide⟩),
   opAt 2164 (.Dup ⟨0, by decide⟩),
   pushAt 2165 0 0,
   opAt 2166 .SUB,
   opAt 2167 .DIV,
   pushAt 2168 1 1,
   opAt 2169 .ADD,
   pushAt 2170 2 1600,
   opAt 2171 .MSTORE,
   opAt 2172 (.Dup ⟨0, by decide⟩),
   opAt 2173 (.Dup ⟨0, by decide⟩),
   pushAt 2174 0 0,
   opAt 2175 .SUB,
   opAt 2176 .MOD,
   pushAt 2177 2 1632,
   opAt 2178 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2179 (.Dup ⟨0, by decide⟩),
   pushAt 2180 1 3,
   opAt 2181 .MUL,
   pushAt 2182 1 2,
   opAt 2183 .XOR,
   opAt 2184 (.Dup ⟨0, by decide⟩),
   opAt 2185 (.Dup ⟨2, by decide⟩),
   opAt 2186 .MUL,
   pushAt 2187 1 2,
   opAt 2188 .SUB,
   opAt 2189 .MUL,
   opAt 2190 (.Dup ⟨0, by decide⟩),
   opAt 2191 (.Dup ⟨2, by decide⟩),
   opAt 2192 .MUL,
   pushAt 2193 1 2,
   opAt 2194 .SUB,
   opAt 2195 .MUL,
   opAt 2196 (.Dup ⟨0, by decide⟩),
   opAt 2197 (.Dup ⟨2, by decide⟩),
   opAt 2198 .MUL,
   pushAt 2199 1 2,
   opAt 2200 .SUB,
   opAt 2201 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2202 (.Dup ⟨0, by decide⟩),
   opAt 2203 (.Dup ⟨2, by decide⟩),
   opAt 2204 .MUL,
   pushAt 2205 1 2,
   opAt 2206 .SUB,
   opAt 2207 .MUL,
   opAt 2208 (.Dup ⟨0, by decide⟩),
   opAt 2209 (.Dup ⟨2, by decide⟩),
   opAt 2210 .MUL,
   pushAt 2211 1 2,
   opAt 2212 .SUB,
   opAt 2213 .MUL,
   opAt 2214 (.Dup ⟨0, by decide⟩),
   opAt 2215 (.Dup ⟨2, by decide⟩),
   opAt 2216 .MUL,
   pushAt 2217 1 2,
   opAt 2218 .SUB,
   opAt 2219 .MUL,
   pushAt 2220 2 1664,
   opAt 2221 .MSTORE,
   opAt 2222 .POP,
   opAt 2223 .POP,
   opAt 2224 .POP,
   opAt 2225 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2257 .JUMPDEST,
   opAt 2258 (.Dup ⟨0, by decide⟩),
   opAt 2259 .ISZERO,
   pushAt 2260 2 3493,
   opAt 2261 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2262 (.Dup ⟨1, by decide⟩),
   pushAt 2263 2 2112,
   pushAt 2264 2 2080,
   opAt 2265 .MCOPY,
   pushAt 2266 0 0,
   pushAt 2267 2 2784,
   opAt 2268 .MLOAD,
   opAt 2269 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2270 2 2080,
   opAt 2271 .MLOAD,
   pushAt 2272 2 1536,
   opAt 2273 .MLOAD,
   opAt 2274 (.Dup ⟨1, by decide⟩),
   opAt 2275 .DIV,
   opAt 2276 (.Swap ⟨0, by decide⟩),
   pushAt 2277 2 1600,
   opAt 2278 .MLOAD,
   opAt 2279 .MUL,
   pushAt 2280 2 1536,
   opAt 2281 .MLOAD,
   pushAt 2282 2 2112,
   opAt 2283 .MLOAD,
   opAt 2284 .DIV,
   opAt 2285 .ADD,
   pushAt 2286 2 1568,
   opAt 2287 .MLOAD,
   opAt 2288 (.Dup ⟨0, by decide⟩),
   pushAt 2289 2 1632,
   opAt 2290 .MLOAD,
   opAt 2291 (.Dup ⟨4, by decide⟩),
   opAt 2292 .MULMOD,
   opAt 2293 (.Dup ⟨2, by decide⟩),
   opAt 2294 .ADDMOD,
   opAt 2295 (.Swap ⟨0, by decide⟩),
   opAt 2296 .SUB,
   pushAt 2297 2 1664,
   opAt 2298 .MLOAD,
   opAt 2299 .MUL,
   opAt 2300 (.Dup ⟨0, by decide⟩),
   pushAt 2301 0 0,
   opAt 2302 .MLOAD,
   opAt 2303 .MUL,
   pushAt 2304 2 2112,
   opAt 2305 .MLOAD,
   opAt 2306 .SUB,
   pushAt 2307 1 32,
   opAt 2308 .MLOAD,
   pushAt 2309 1 128,
   opAt 2310 .SHR,
   opAt 2311 (.Dup ⟨2, by decide⟩),
   pushAt 2312 1 128,
   opAt 2313 .SHR,
   opAt 2314 .MUL,
   opAt 2315 .GT,
   opAt 2316 (.Swap ⟨0, by decide⟩),
   opAt 2317 .SUB,
   opAt 2318 (.Swap ⟨0, by decide⟩),
   pushAt 2319 2 1568,
   opAt 2320 .MLOAD,
   opAt 2321 .GT,
   opAt 2322 .ISZERO,
   pushAt 2323 0 0,
   opAt 2324 .SUB,
   opAt 2325 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2326 0 0,
   pushAt 2327 1 31,
   opAt 2328 .NOT,
   pushAt 2329 0 0,
   opAt 2330 .NOT,
   pushAt 2331 2 2784,
   opAt 2332 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2336 .JUMPDEST,
   pushAt 2337 2 832,
   opAt 2338 (.Dup ⟨1, by decide⟩),
   opAt 2339 .SUB,
   opAt 2340 .MLOAD,
   opAt 2341 (.Dup ⟨2, by decide⟩),
   opAt 2342 (.Dup ⟨6, by decide⟩),
   opAt 2343 (.Dup ⟨2, by decide⟩),
   opAt 2344 .MUL,
   opAt 2345 (.Swap ⟨1, by decide⟩),
   opAt 2346 (.Dup ⟨7, by decide⟩),
   opAt 2347 .MULMOD,
   opAt 2348 (.Dup ⟨1, by decide⟩),
   opAt 2349 (.Dup ⟨1, by decide⟩),
   opAt 2350 .LT,
   opAt 2351 .SUB,
   opAt 2352 (.Dup ⟨5, by decide⟩),
   opAt 2353 (.Dup ⟨2, by decide⟩),
   opAt 2354 .ADD,
   opAt 2355 (.Dup ⟨0, by decide⟩),
   opAt 2356 (.Swap ⟨6, by decide⟩),
   opAt 2357 .GT,
   opAt 2358 .SUB,
   opAt 2359 .SUB,
   opAt 2360 (.Dup ⟨4, by decide⟩),
   opAt 2361 (.Dup ⟨2, by decide⟩),
   opAt 2362 .MLOAD,
   opAt 2363 .ADD,
   opAt 2364 (.Dup ⟨0, by decide⟩),
   opAt 2365 (.Swap ⟨5, by decide⟩),
   opAt 2366 .GT,
   opAt 2367 .ADD,
   opAt 2368 (.Swap ⟨3, by decide⟩),
   opAt 2369 (.Dup ⟨1, by decide⟩),
   opAt 2370 .MSTORE,
   opAt 2371 (.Dup ⟨2, by decide⟩),
   opAt 2372 .ADD,
   pushAt 2484 2 2080,
   opAt 2485 (.Dup ⟨1, by decide⟩),
   opAt 2486 .GT,
   pushAt 2487 2 3144,
   opAt 2488 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2489 .POP,
   opAt 2490 .POP,
   opAt 2491 .POP,
   pushAt 2492 2 2080,
   opAt 2493 .MLOAD,
   opAt 2494 (.Dup ⟨1, by decide⟩),
   opAt 2495 .ADD,
   opAt 2496 (.Dup ⟨0, by decide⟩),
   opAt 2497 (.Swap ⟨1, by decide⟩),
   opAt 2498 .GT,
   opAt 2499 (.Dup ⟨1, by decide⟩),
   opAt 2500 (.Dup ⟨3, by decide⟩),
   opAt 2501 .GT,
   opAt 2502 .GT,
   opAt 2503 (.Swap ⟨1, by decide⟩),
   opAt 2504 (.Swap ⟨0, by decide⟩),
   opAt 2505 .SUB,
   opAt 2506 (.Dup ⟨0, by decide⟩),
   pushAt 2507 2 2080,
   opAt 2508 .MSTORE,
   opAt 2509 (.Dup ⟨1, by decide⟩),
   opAt 2510 .OR,
   pushAt 2511 2 3349,
   opAt 2512 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2519 .JUMPDEST,
   opAt 2520 .ISZERO,
   pushAt 2521 2 3434,
   opAt 2522 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2523 .JUMPDEST,
   pushAt 2524 0 0,
   pushAt 2525 2 2784,
   opAt 2526 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2527 .JUMPDEST,
   opAt 2528 (.Dup ⟨0, by decide⟩),
   opAt 2529 .MLOAD,
   opAt 2530 (.Dup ⟨1, by decide⟩),
   pushAt 2531 2 2112,
   opAt 2532 (.Swap ⟨0, by decide⟩),
   opAt 2533 .SUB,
   opAt 2534 .MLOAD,
   opAt 2535 (.Dup ⟨1, by decide⟩),
   opAt 2536 .ADD,
   opAt 2537 (.Dup ⟨0, by decide⟩),
   opAt 2538 (.Dup ⟨2, by decide⟩),
   opAt 2539 .GT,
   opAt 2540 (.Swap ⟨1, by decide⟩),
   opAt 2541 .POP,
   opAt 2542 (.Dup ⟨3, by decide⟩),
   opAt 2543 .ADD,
   opAt 2544 (.Dup ⟨0, by decide⟩),
   opAt 2545 (.Dup ⟨4, by decide⟩),
   opAt 2546 .GT,
   opAt 2547 (.Swap ⟨3, by decide⟩),
   opAt 2548 .POP,
   opAt 2549 (.Dup ⟨2, by decide⟩),
   opAt 2550 .MSTORE,
   opAt 2551 (.Swap ⟨0, by decide⟩),
   opAt 2552 (.Swap ⟨1, by decide⟩),
   opAt 2553 .OR,
   opAt 2554 (.Swap ⟨0, by decide⟩),
   pushAt 2555 1 31,
   opAt 2556 .NOT,
   opAt 2557 .ADD,
   pushAt 2558 2 2111,
   opAt 2559 (.Dup ⟨1, by decide⟩),
   opAt 2560 .GT,
   pushAt 2561 2 3361,
   opAt 2562 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2563 .POP,
   pushAt 2564 2 2080,
   opAt 2565 .MLOAD,
   opAt 2566 (.Dup ⟨1, by decide⟩),
   opAt 2567 .ADD,
   opAt 2568 (.Dup ⟨0, by decide⟩),
   pushAt 2569 2 2080,
   opAt 2570 .MSTORE,
   opAt 2571 .LT,
   opAt 2572 .ISZERO,
   pushAt 2573 2 3355,
   opAt 2574 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2575 .JUMPDEST,
   pushAt 2576 2 2080,
   opAt 2577 .MLOAD,
   opAt 2578 (.Dup ⟨0, by decide⟩),
   opAt 2579 .ISZERO,
   pushAt 2580 2 3339,
   opAt 2581 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2575 .JUMPDEST,
   pushAt 2576 2 2080,
   opAt 2577 .MLOAD,
   opAt 2578 (.Dup ⟨0, by decide⟩),
   opAt 2579 .ISZERO,
   pushAt 2580 2 3339,
   opAt 2581 .JUMPI,
   opAt 2582 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .JUMPDEST,
   pushAt 2584 0 0,
   pushAt 2585 2 2784,
   opAt 2586 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2587 .JUMPDEST,
   opAt 2588 (.Dup ⟨0, by decide⟩),
   opAt 2589 .MLOAD,
   pushAt 2590 2 2112,
   opAt 2591 (.Dup ⟨2, by decide⟩),
   opAt 2592 .SUB,
   opAt 2593 .MLOAD,
   opAt 2594 (.Dup ⟨1, by decide⟩),
   opAt 2595 (.Dup ⟨1, by decide⟩),
   opAt 2596 .GT,
   opAt 2597 (.Swap ⟨1, by decide⟩),
   opAt 2598 .SUB,
   opAt 2599 (.Dup ⟨3, by decide⟩),
   opAt 2600 (.Dup ⟨1, by decide⟩),
   opAt 2601 .LT,
   opAt 2602 (.Swap ⟨0, by decide⟩),
   opAt 2603 (.Dup ⟨4, by decide⟩),
   opAt 2604 (.Swap ⟨0, by decide⟩),
   opAt 2605 .SUB,
   opAt 2606 (.Dup ⟨3, by decide⟩),
   opAt 2607 .MSTORE,
   opAt 2608 .OR,
   opAt 2609 (.Swap ⟨1, by decide⟩),
   opAt 2610 .POP,
   pushAt 2611 1 31,
   opAt 2612 .NOT,
   opAt 2613 .ADD,
   pushAt 2614 2 2111,
   opAt 2615 (.Dup ⟨1, by decide⟩),
   opAt 2616 .GT,
   pushAt 2617 2 3440,
   opAt 2618 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2619 .POP,
   pushAt 2620 2 2080,
   opAt 2621 .MLOAD,
   opAt 2622 .SUB,
   pushAt 2623 2 2080,
   opAt 2624 .MSTORE,
   pushAt 2625 2 3422,
   opAt 2626 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2513 .JUMPDEST,
   opAt 2514 .NOT,
   opAt 2515 .ADD,
   pushAt 2516 2 3029,
   pushAt 2517 2 4486,
   opAt 2518 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2647 (.Dup ⟨0, by decide⟩),
   pushAt 2648 2 2112,
   pushAt 2649 2 512,
   opAt 2650 .MCOPY,
   opAt 2651 (.Dup ⟨0, by decide⟩),
   pushAt 2652 2 1280,
   pushAt 2653 2 1024,
   opAt 2654 .MCOPY,
   pushAt 2655 2 2636,
   opAt 2656 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2793 = true :=
  Artifact.isValidJumpDest_index 2086 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2827 = true :=
  Artifact.isValidJumpDest_index 2108 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2844 = true :=
  Artifact.isValidJumpDest_index 2116 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2859 = true :=
  Artifact.isValidJumpDest_index 2124 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3029 = true :=
  Artifact.isValidJumpDest_index 2257 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3144 = true :=
  Artifact.isValidJumpDest_index 2336 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3355 = true :=
  Artifact.isValidJumpDest_index 2523 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3361 = true :=
  Artifact.isValidJumpDest_index 2527 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3422 = true :=
  Artifact.isValidJumpDest_index 2575 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3440 = true :=
  Artifact.isValidJumpDest_index 2587 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3349 = true :=
  Artifact.isValidJumpDest_index 2519 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3434 = true :=
  Artifact.isValidJumpDest_index 2583 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3339 = true :=
  Artifact.isValidJumpDest_index 2513 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3493 = true :=
  Artifact.isValidJumpDest_index 2627 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
