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
   pushAt 2112 2 4335,
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
   pushAt 2262 2 3501,
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
   opAt 2279 .JUMPDEST,
   opAt 2280 .JUMPDEST,
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
  [opAt 2340 .JUMPDEST,
   pushAt 2341 2 832,
   opAt 2342 (.Dup ⟨1, by decide⟩),
   opAt 2343 .SUB,
   opAt 2344 .MLOAD,
   opAt 2345 (.Dup ⟨2, by decide⟩),
   opAt 2346 (.Dup ⟨6, by decide⟩),
   opAt 2347 (.Dup ⟨2, by decide⟩),
   opAt 2348 .MUL,
   opAt 2349 (.Swap ⟨1, by decide⟩),
   opAt 2350 (.Dup ⟨7, by decide⟩),
   opAt 2351 .MULMOD,
   opAt 2352 (.Dup ⟨1, by decide⟩),
   opAt 2353 (.Dup ⟨1, by decide⟩),
   opAt 2354 .LT,
   opAt 2355 .SUB,
   opAt 2356 (.Dup ⟨5, by decide⟩),
   opAt 2357 (.Dup ⟨2, by decide⟩),
   opAt 2358 .ADD,
   opAt 2359 (.Dup ⟨0, by decide⟩),
   opAt 2360 (.Swap ⟨6, by decide⟩),
   opAt 2361 .GT,
   opAt 2362 .SUB,
   opAt 2363 .SUB,
   opAt 2364 (.Dup ⟨4, by decide⟩),
   opAt 2365 (.Dup ⟨2, by decide⟩),
   opAt 2366 .MLOAD,
   opAt 2367 .ADD,
   opAt 2368 (.Dup ⟨0, by decide⟩),
   opAt 2369 (.Swap ⟨5, by decide⟩),
   opAt 2370 .GT,
   opAt 2371 .ADD,
   opAt 2372 (.Swap ⟨3, by decide⟩),
   opAt 2373 (.Dup ⟨1, by decide⟩),
   opAt 2374 .MSTORE,
   opAt 2375 (.Dup ⟨2, by decide⟩),
   opAt 2376 .ADD,
   pushAt 2488 2 2080,
   opAt 2489 (.Dup ⟨1, by decide⟩),
   opAt 2490 .GT,
   pushAt 2491 2 3149,
   opAt 2492 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2493 .POP,
   opAt 2494 .POP,
   opAt 2495 .POP,
   pushAt 2496 2 2080,
   opAt 2497 .MLOAD,
   opAt 2498 (.Dup ⟨1, by decide⟩),
   opAt 2499 .ADD,
   opAt 2500 (.Dup ⟨0, by decide⟩),
   opAt 2501 (.Swap ⟨1, by decide⟩),
   opAt 2502 .GT,
   opAt 2503 (.Dup ⟨1, by decide⟩),
   opAt 2504 (.Dup ⟨3, by decide⟩),
   opAt 2505 .GT,
   opAt 2506 .GT,
   opAt 2507 (.Swap ⟨1, by decide⟩),
   opAt 2508 (.Swap ⟨0, by decide⟩),
   opAt 2509 .SUB,
   opAt 2510 (.Dup ⟨0, by decide⟩),
   pushAt 2511 2 2080,
   opAt 2512 .MSTORE,
   opAt 2513 (.Dup ⟨1, by decide⟩),
   opAt 2514 .OR,
   pushAt 2515 2 3357,
   opAt 2516 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2524 .JUMPDEST,
   opAt 2525 .ISZERO,
   pushAt 2526 2 3442,
   opAt 2527 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2528 .JUMPDEST,
   pushAt 2529 0 0,
   pushAt 2530 2 2784,
   opAt 2531 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2532 .JUMPDEST,
   opAt 2533 (.Dup ⟨0, by decide⟩),
   opAt 2534 .MLOAD,
   opAt 2535 .JUMPDEST,
   pushAt 2536 2 2112,
   opAt 2537 (.Dup ⟨2, by decide⟩),
   opAt 2538 .SUB,
   opAt 2539 .MLOAD,
   opAt 2540 (.Dup ⟨1, by decide⟩),
   opAt 2541 .ADD,
   opAt 2542 (.Dup ⟨0, by decide⟩),
   opAt 2543 (.Dup ⟨2, by decide⟩),
   opAt 2544 .GT,
   opAt 2545 (.Swap ⟨1, by decide⟩),
   opAt 2546 .POP,
   opAt 2547 (.Dup ⟨3, by decide⟩),
   opAt 2548 .ADD,
   opAt 2549 (.Dup ⟨0, by decide⟩),
   opAt 2550 (.Dup ⟨4, by decide⟩),
   opAt 2551 .GT,
   opAt 2552 (.Swap ⟨3, by decide⟩),
   opAt 2553 .POP,
   opAt 2554 (.Dup ⟨2, by decide⟩),
   opAt 2555 .MSTORE,
   opAt 2556 (.Swap ⟨0, by decide⟩),
   opAt 2557 (.Swap ⟨1, by decide⟩),
   opAt 2558 .OR,
   opAt 2559 (.Swap ⟨0, by decide⟩),
   pushAt 2560 1 31,
   opAt 2561 .NOT,
   opAt 2562 .ADD,
   pushAt 2563 2 2111,
   opAt 2564 (.Dup ⟨1, by decide⟩),
   opAt 2565 .GT,
   pushAt 2566 2 3369,
   opAt 2567 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2568 .POP,
   pushAt 2569 2 2080,
   opAt 2570 .MLOAD,
   opAt 2571 (.Dup ⟨1, by decide⟩),
   opAt 2572 .ADD,
   opAt 2573 (.Dup ⟨0, by decide⟩),
   pushAt 2574 2 2080,
   opAt 2575 .MSTORE,
   opAt 2576 .LT,
   opAt 2577 .ISZERO,
   pushAt 2578 2 3363,
   opAt 2579 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2580 .JUMPDEST,
   pushAt 2581 2 2080,
   opAt 2582 .MLOAD,
   opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 .ISZERO,
   pushAt 2585 2 3344,
   opAt 2586 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2580 .JUMPDEST,
   pushAt 2581 2 2080,
   opAt 2582 .MLOAD,
   opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 .ISZERO,
   pushAt 2585 2 3344,
   opAt 2586 .JUMPI,
   opAt 2587 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2588 .JUMPDEST,
   pushAt 2589 0 0,
   pushAt 2590 2 2784,
   opAt 2591 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2592 .JUMPDEST,
   opAt 2593 (.Dup ⟨0, by decide⟩),
   opAt 2594 .MLOAD,
   pushAt 2595 2 2112,
   opAt 2596 (.Dup ⟨2, by decide⟩),
   opAt 2597 .SUB,
   opAt 2598 .MLOAD,
   opAt 2599 (.Dup ⟨1, by decide⟩),
   opAt 2600 (.Dup ⟨1, by decide⟩),
   opAt 2601 .GT,
   opAt 2602 (.Swap ⟨1, by decide⟩),
   opAt 2603 .SUB,
   opAt 2604 (.Dup ⟨3, by decide⟩),
   opAt 2605 (.Dup ⟨1, by decide⟩),
   opAt 2606 .LT,
   opAt 2607 (.Swap ⟨0, by decide⟩),
   opAt 2608 (.Dup ⟨4, by decide⟩),
   opAt 2609 (.Swap ⟨0, by decide⟩),
   opAt 2610 .SUB,
   opAt 2611 (.Dup ⟨3, by decide⟩),
   opAt 2612 .MSTORE,
   opAt 2613 .OR,
   opAt 2614 (.Swap ⟨1, by decide⟩),
   opAt 2615 .POP,
   pushAt 2616 1 31,
   opAt 2617 .NOT,
   opAt 2618 .ADD,
   pushAt 2619 2 2111,
   opAt 2620 (.Dup ⟨1, by decide⟩),
   opAt 2621 .GT,
   pushAt 2622 2 3448,
   opAt 2623 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2624 .POP,
   pushAt 2625 2 2080,
   opAt 2626 .MLOAD,
   opAt 2627 .SUB,
   pushAt 2628 2 2080,
   opAt 2629 .MSTORE,
   pushAt 2630 2 3430,
   opAt 2631 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2517 .JUMPDEST,
   opAt 2518 .NOT,
   opAt 2519 .ADD,
   pushAt 2520 2 3032,
   pushAt 2521 2 512,
   pushAt 2522 2 4335,
   opAt 2523 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2652 2 2688,
   opAt 2653 .MLOAD,
   pushAt 2654 2 1280,
   pushAt 2655 2 1024,
   opAt 2656 .MCOPY,
   pushAt 2657 2 2637,
   opAt 2658 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3149 = true :=
  Artifact.isValidJumpDest_index 2340 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3363 = true :=
  Artifact.isValidJumpDest_index 2528 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3369 = true :=
  Artifact.isValidJumpDest_index 2532 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3430 = true :=
  Artifact.isValidJumpDest_index 2580 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3448 = true :=
  Artifact.isValidJumpDest_index 2592 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3357 = true :=
  Artifact.isValidJumpDest_index 2524 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3442 = true :=
  Artifact.isValidJumpDest_index 2588 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3344 = true :=
  Artifact.isValidJumpDest_index 2517 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3501 = true :=
  Artifact.isValidJumpDest_index 2632 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
