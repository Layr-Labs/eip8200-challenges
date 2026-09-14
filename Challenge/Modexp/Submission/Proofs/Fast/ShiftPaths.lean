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
   pushAt 2094 2 2822,
   opAt 2095 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2096 (.Dup ⟨0, by decide⟩),
   pushAt 2097 1 96,
   pushAt 2098 2 2112,
   opAt 2099 .CALLDATACOPY,
   pushAt 2100 0 0,
   pushAt 2101 2 2080,
   opAt 2102 .MSTORE,
   pushAt 2103 2 2839,
   pushAt 2104 2 4521,
   opAt 2105 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2106 .JUMPDEST,
   pushAt 2107 1 1,
   pushAt 2108 2 1024,
   opAt 2109 .MSTORE,
   pushAt 2110 2 881,
   pushAt 2111 2 1024,
   pushAt 2112 2 1658,
   opAt 2113 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2119 1 1,
   pushAt 2120 2 2752,
   opAt 2121 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2143 .POP,
   opAt 2144 .POP,
   pushAt 2145 0 0,
   opAt 2146 .MLOAD,
   opAt 2147 (.Dup ⟨0, by decide⟩),
   pushAt 2148 0 0,
   opAt 2149 .SUB,
   opAt 2150 (.Dup ⟨1, by decide⟩),
   opAt 2151 .AND,
   opAt 2152 (.Dup ⟨0, by decide⟩),
   pushAt 2153 2 1536,
   opAt 2154 .MSTORE,
   opAt 2155 (.Dup ⟨0, by decide⟩),
   opAt 2156 (.Dup ⟨2, by decide⟩),
   opAt 2157 .DIV,
   opAt 2158 (.Dup ⟨0, by decide⟩),
   pushAt 2159 2 1568,
   opAt 2160 .MSTORE,
   opAt 2161 (.Dup ⟨1, by decide⟩),
   opAt 2162 (.Dup ⟨0, by decide⟩),
   pushAt 2163 0 0,
   opAt 2164 .SUB,
   opAt 2165 .DIV,
   pushAt 2166 1 1,
   opAt 2167 .ADD,
   pushAt 2168 2 1600,
   opAt 2169 .MSTORE,
   opAt 2170 (.Dup ⟨0, by decide⟩),
   opAt 2171 (.Dup ⟨0, by decide⟩),
   pushAt 2172 0 0,
   opAt 2173 .SUB,
   opAt 2174 .MOD,
   pushAt 2175 2 1632,
   opAt 2176 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2177 (.Dup ⟨0, by decide⟩),
   pushAt 2178 1 3,
   opAt 2179 .MUL,
   pushAt 2180 1 2,
   opAt 2181 .XOR,
   opAt 2182 (.Dup ⟨0, by decide⟩),
   opAt 2183 (.Dup ⟨2, by decide⟩),
   opAt 2184 .MUL,
   pushAt 2185 1 2,
   opAt 2186 .SUB,
   opAt 2187 .MUL,
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
   opAt 2199 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2200 (.Dup ⟨0, by decide⟩),
   opAt 2201 (.Dup ⟨2, by decide⟩),
   opAt 2202 .MUL,
   pushAt 2203 1 2,
   opAt 2204 .SUB,
   opAt 2205 .MUL,
   opAt 2206 (.Dup ⟨0, by decide⟩),
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
   pushAt 2218 2 1664,
   opAt 2219 .MSTORE,
   opAt 2220 .POP,
   opAt 2221 .POP,
   opAt 2222 .POP,
   opAt 2223 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2255 .JUMPDEST,
   opAt 2256 (.Dup ⟨0, by decide⟩),
   opAt 2257 .ISZERO,
   pushAt 2258 2 3488,
   opAt 2259 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2260 (.Dup ⟨1, by decide⟩),
   pushAt 2261 2 2112,
   pushAt 2262 2 2080,
   opAt 2263 .MCOPY,
   pushAt 2264 0 0,
   pushAt 2265 2 2784,
   opAt 2266 .MLOAD,
   opAt 2267 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2268 2 2080,
   opAt 2269 .MLOAD,
   pushAt 2270 2 1536,
   opAt 2271 .MLOAD,
   opAt 2272 (.Dup ⟨1, by decide⟩),
   opAt 2273 .DIV,
   opAt 2274 (.Swap ⟨0, by decide⟩),
   pushAt 2275 2 1600,
   opAt 2276 .MLOAD,
   opAt 2277 .MUL,
   pushAt 2278 2 1536,
   opAt 2279 .MLOAD,
   pushAt 2280 2 2112,
   opAt 2281 .MLOAD,
   opAt 2282 .DIV,
   opAt 2283 .ADD,
   pushAt 2284 2 1568,
   opAt 2285 .MLOAD,
   opAt 2286 (.Dup ⟨0, by decide⟩),
   pushAt 2287 2 1632,
   opAt 2288 .MLOAD,
   opAt 2289 (.Dup ⟨4, by decide⟩),
   opAt 2290 .MULMOD,
   opAt 2291 (.Dup ⟨2, by decide⟩),
   opAt 2292 .ADDMOD,
   opAt 2293 (.Swap ⟨0, by decide⟩),
   opAt 2294 .SUB,
   pushAt 2295 2 1664,
   opAt 2296 .MLOAD,
   opAt 2297 .MUL,
   opAt 2298 (.Dup ⟨0, by decide⟩),
   pushAt 2299 0 0,
   opAt 2300 .MLOAD,
   opAt 2301 .MUL,
   pushAt 2302 2 2112,
   opAt 2303 .MLOAD,
   opAt 2304 .SUB,
   pushAt 2305 1 32,
   opAt 2306 .MLOAD,
   pushAt 2307 1 128,
   opAt 2308 .SHR,
   opAt 2309 (.Dup ⟨2, by decide⟩),
   pushAt 2310 1 128,
   opAt 2311 .SHR,
   opAt 2312 .MUL,
   opAt 2313 .GT,
   opAt 2314 (.Swap ⟨0, by decide⟩),
   opAt 2315 .SUB,
   opAt 2316 (.Swap ⟨0, by decide⟩),
   pushAt 2317 2 1568,
   opAt 2318 .MLOAD,
   opAt 2319 .GT,
   opAt 2320 .ISZERO,
   pushAt 2321 0 0,
   opAt 2322 .SUB,
   opAt 2323 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2324 0 0,
   pushAt 2325 1 31,
   opAt 2326 .NOT,
   pushAt 2327 0 0,
   opAt 2328 .NOT,
   pushAt 2329 2 2784,
   opAt 2330 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2334 .JUMPDEST,
   pushAt 2335 2 832,
   opAt 2336 (.Dup ⟨1, by decide⟩),
   opAt 2337 .SUB,
   opAt 2338 .MLOAD,
   opAt 2339 (.Dup ⟨2, by decide⟩),
   opAt 2340 (.Dup ⟨6, by decide⟩),
   opAt 2341 (.Dup ⟨2, by decide⟩),
   opAt 2342 .MUL,
   opAt 2343 (.Swap ⟨1, by decide⟩),
   opAt 2344 (.Dup ⟨7, by decide⟩),
   opAt 2345 .MULMOD,
   opAt 2346 (.Dup ⟨1, by decide⟩),
   opAt 2347 (.Dup ⟨1, by decide⟩),
   opAt 2348 .LT,
   opAt 2349 .SUB,
   opAt 2350 (.Dup ⟨5, by decide⟩),
   opAt 2351 (.Dup ⟨2, by decide⟩),
   opAt 2352 .ADD,
   opAt 2353 (.Dup ⟨0, by decide⟩),
   opAt 2354 (.Swap ⟨6, by decide⟩),
   opAt 2355 .GT,
   opAt 2356 .SUB,
   opAt 2357 .SUB,
   opAt 2358 (.Dup ⟨4, by decide⟩),
   opAt 2359 (.Dup ⟨2, by decide⟩),
   opAt 2360 .MLOAD,
   opAt 2361 .ADD,
   opAt 2362 (.Dup ⟨0, by decide⟩),
   opAt 2363 (.Swap ⟨5, by decide⟩),
   opAt 2364 .GT,
   opAt 2365 .ADD,
   opAt 2366 (.Swap ⟨3, by decide⟩),
   opAt 2367 (.Dup ⟨1, by decide⟩),
   opAt 2368 .MSTORE,
   opAt 2369 (.Dup ⟨2, by decide⟩),
   opAt 2370 .ADD,
   pushAt 2482 2 2080,
   opAt 2483 (.Dup ⟨1, by decide⟩),
   opAt 2484 .GT,
   pushAt 2485 2 3139,
   opAt 2486 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2487 .POP,
   opAt 2488 .POP,
   opAt 2489 .POP,
   pushAt 2490 2 2080,
   opAt 2491 .MLOAD,
   opAt 2492 (.Dup ⟨1, by decide⟩),
   opAt 2493 .ADD,
   opAt 2494 (.Dup ⟨0, by decide⟩),
   opAt 2495 (.Swap ⟨1, by decide⟩),
   opAt 2496 .GT,
   opAt 2497 (.Dup ⟨1, by decide⟩),
   opAt 2498 (.Dup ⟨3, by decide⟩),
   opAt 2499 .GT,
   opAt 2500 .GT,
   opAt 2501 (.Swap ⟨1, by decide⟩),
   opAt 2502 (.Swap ⟨0, by decide⟩),
   opAt 2503 .SUB,
   opAt 2504 (.Dup ⟨0, by decide⟩),
   pushAt 2505 2 2080,
   opAt 2506 .MSTORE,
   opAt 2507 (.Dup ⟨1, by decide⟩),
   opAt 2508 .OR,
   pushAt 2509 2 3344,
   opAt 2510 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2517 .JUMPDEST,
   opAt 2518 .ISZERO,
   pushAt 2519 2 3429,
   opAt 2520 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2521 .JUMPDEST,
   pushAt 2522 0 0,
   pushAt 2523 2 2784,
   opAt 2524 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2525 .JUMPDEST,
   opAt 2526 (.Dup ⟨0, by decide⟩),
   opAt 2527 .MLOAD,
   opAt 2528 (.Dup ⟨1, by decide⟩),
   pushAt 2529 2 2112,
   opAt 2530 (.Swap ⟨0, by decide⟩),
   opAt 2531 .SUB,
   opAt 2532 .MLOAD,
   opAt 2533 (.Dup ⟨1, by decide⟩),
   opAt 2534 .ADD,
   opAt 2535 (.Dup ⟨0, by decide⟩),
   opAt 2536 (.Dup ⟨2, by decide⟩),
   opAt 2537 .GT,
   opAt 2538 (.Swap ⟨1, by decide⟩),
   opAt 2539 .POP,
   opAt 2540 (.Dup ⟨3, by decide⟩),
   opAt 2541 .ADD,
   opAt 2542 (.Dup ⟨0, by decide⟩),
   opAt 2543 (.Dup ⟨4, by decide⟩),
   opAt 2544 .GT,
   opAt 2545 (.Swap ⟨3, by decide⟩),
   opAt 2546 .POP,
   opAt 2547 (.Dup ⟨2, by decide⟩),
   opAt 2548 .MSTORE,
   opAt 2549 (.Swap ⟨0, by decide⟩),
   opAt 2550 (.Swap ⟨1, by decide⟩),
   opAt 2551 .OR,
   opAt 2552 (.Swap ⟨0, by decide⟩),
   pushAt 2553 1 31,
   opAt 2554 .NOT,
   opAt 2555 .ADD,
   pushAt 2556 2 2111,
   opAt 2557 (.Dup ⟨1, by decide⟩),
   opAt 2558 .GT,
   pushAt 2559 2 3356,
   opAt 2560 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2561 .POP,
   pushAt 2562 2 2080,
   opAt 2563 .MLOAD,
   opAt 2564 (.Dup ⟨1, by decide⟩),
   opAt 2565 .ADD,
   opAt 2566 (.Dup ⟨0, by decide⟩),
   pushAt 2567 2 2080,
   opAt 2568 .MSTORE,
   opAt 2569 .LT,
   opAt 2570 .ISZERO,
   pushAt 2571 2 3350,
   opAt 2572 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2573 .JUMPDEST,
   pushAt 2574 2 2080,
   opAt 2575 .MLOAD,
   opAt 2576 (.Dup ⟨0, by decide⟩),
   opAt 2577 .ISZERO,
   pushAt 2578 2 3334,
   opAt 2579 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2573 .JUMPDEST,
   pushAt 2574 2 2080,
   opAt 2575 .MLOAD,
   opAt 2576 (.Dup ⟨0, by decide⟩),
   opAt 2577 .ISZERO,
   pushAt 2578 2 3334,
   opAt 2579 .JUMPI,
   opAt 2580 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2581 .JUMPDEST,
   pushAt 2582 0 0,
   pushAt 2583 2 2784,
   opAt 2584 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2585 .JUMPDEST,
   opAt 2586 (.Dup ⟨0, by decide⟩),
   opAt 2587 .MLOAD,
   pushAt 2588 2 2112,
   opAt 2589 (.Dup ⟨2, by decide⟩),
   opAt 2590 .SUB,
   opAt 2591 .MLOAD,
   opAt 2592 (.Dup ⟨1, by decide⟩),
   opAt 2593 (.Dup ⟨1, by decide⟩),
   opAt 2594 .GT,
   opAt 2595 (.Swap ⟨1, by decide⟩),
   opAt 2596 .SUB,
   opAt 2597 (.Dup ⟨3, by decide⟩),
   opAt 2598 (.Dup ⟨1, by decide⟩),
   opAt 2599 .LT,
   opAt 2600 (.Swap ⟨0, by decide⟩),
   opAt 2601 (.Dup ⟨4, by decide⟩),
   opAt 2602 (.Swap ⟨0, by decide⟩),
   opAt 2603 .SUB,
   opAt 2604 (.Dup ⟨3, by decide⟩),
   opAt 2605 .MSTORE,
   opAt 2606 .OR,
   opAt 2607 (.Swap ⟨1, by decide⟩),
   opAt 2608 .POP,
   pushAt 2609 1 31,
   opAt 2610 .NOT,
   opAt 2611 .ADD,
   pushAt 2612 2 2111,
   opAt 2613 (.Dup ⟨1, by decide⟩),
   opAt 2614 .GT,
   pushAt 2615 2 3435,
   opAt 2616 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2617 .POP,
   pushAt 2618 2 2080,
   opAt 2619 .MLOAD,
   opAt 2620 .SUB,
   pushAt 2621 2 2080,
   opAt 2622 .MSTORE,
   pushAt 2623 2 3417,
   opAt 2624 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2511 .JUMPDEST,
   opAt 2512 .NOT,
   opAt 2513 .ADD,
   pushAt 2514 2 3024,
   pushAt 2515 2 4521,
   opAt 2516 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2645 (.Dup ⟨0, by decide⟩),
   pushAt 2646 2 2112,
   pushAt 2647 2 512,
   opAt 2648 .MCOPY,
   opAt 2649 (.Dup ⟨0, by decide⟩),
   pushAt 2650 2 1280,
   pushAt 2651 2 1024,
   opAt 2652 .MCOPY,
   pushAt 2653 2 2631,
   opAt 2654 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2788 = true :=
  Artifact.isValidJumpDest_index 2084 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2822 = true :=
  Artifact.isValidJumpDest_index 2106 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2839 = true :=
  Artifact.isValidJumpDest_index 2114 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2854 = true :=
  Artifact.isValidJumpDest_index 2122 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3024 = true :=
  Artifact.isValidJumpDest_index 2255 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3139 = true :=
  Artifact.isValidJumpDest_index 2334 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3350 = true :=
  Artifact.isValidJumpDest_index 2521 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3356 = true :=
  Artifact.isValidJumpDest_index 2525 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3417 = true :=
  Artifact.isValidJumpDest_index 2573 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3435 = true :=
  Artifact.isValidJumpDest_index 2585 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3344 = true :=
  Artifact.isValidJumpDest_index 2517 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3429 = true :=
  Artifact.isValidJumpDest_index 2581 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3334 = true :=
  Artifact.isValidJumpDest_index 2511 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3488 = true :=
  Artifact.isValidJumpDest_index 2625 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
