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
  [opAt 2073 .JUMPDEST,
   opAt 2074 (.Dup ⟨0, by decide⟩),
   opAt 2075 (.Dup ⟨3, by decide⟩),
   opAt 2076 .EQ,
   pushAt 2077 0 0,
   opAt 2078 .MLOAD,
   pushAt 2079 1 255,
   opAt 2080 .SHR,
   opAt 2081 .AND,
   opAt 2082 .ISZERO,
   pushAt 2083 2 2822,
   opAt 2084 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2085 (.Dup ⟨0, by decide⟩),
   pushAt 2086 1 96,
   pushAt 2087 2 2112,
   opAt 2088 .CALLDATACOPY,
   pushAt 2089 0 0,
   pushAt 2090 2 2080,
   opAt 2091 .MSTORE,
   pushAt 2092 2 2839,
   pushAt 2093 2 4521,
   opAt 2094 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2095 .JUMPDEST,
   pushAt 2096 1 1,
   pushAt 2097 2 1024,
   opAt 2098 .MSTORE,
   pushAt 2099 2 880,
   pushAt 2100 2 1024,
   pushAt 2101 2 1657,
   opAt 2102 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2108 1 1,
   pushAt 2109 2 2752,
   opAt 2110 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2132 .POP,
   opAt 2133 .POP,
   pushAt 2134 0 0,
   opAt 2135 .MLOAD,
   opAt 2136 (.Dup ⟨0, by decide⟩),
   pushAt 2137 0 0,
   opAt 2138 .SUB,
   opAt 2139 (.Dup ⟨1, by decide⟩),
   opAt 2140 .AND,
   opAt 2141 (.Dup ⟨0, by decide⟩),
   pushAt 2142 2 1536,
   opAt 2143 .MSTORE,
   opAt 2144 (.Dup ⟨0, by decide⟩),
   opAt 2145 (.Dup ⟨2, by decide⟩),
   opAt 2146 .DIV,
   opAt 2147 (.Dup ⟨0, by decide⟩),
   pushAt 2148 2 1568,
   opAt 2149 .MSTORE,
   opAt 2150 (.Dup ⟨1, by decide⟩),
   opAt 2151 (.Dup ⟨0, by decide⟩),
   pushAt 2152 0 0,
   opAt 2153 .SUB,
   opAt 2154 .DIV,
   pushAt 2155 1 1,
   opAt 2156 .ADD,
   pushAt 2157 2 1600,
   opAt 2158 .MSTORE,
   opAt 2159 (.Dup ⟨0, by decide⟩),
   opAt 2160 (.Dup ⟨0, by decide⟩),
   pushAt 2161 0 0,
   opAt 2162 .SUB,
   opAt 2163 .MOD,
   pushAt 2164 2 1632,
   opAt 2165 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2166 (.Dup ⟨0, by decide⟩),
   pushAt 2167 1 3,
   opAt 2168 .MUL,
   pushAt 2169 1 2,
   opAt 2170 .XOR,
   opAt 2171 (.Dup ⟨0, by decide⟩),
   opAt 2172 (.Dup ⟨2, by decide⟩),
   opAt 2173 .MUL,
   pushAt 2174 1 2,
   opAt 2175 .SUB,
   opAt 2176 .MUL,
   opAt 2177 (.Dup ⟨0, by decide⟩),
   opAt 2178 (.Dup ⟨2, by decide⟩),
   opAt 2179 .MUL,
   pushAt 2180 1 2,
   opAt 2181 .SUB,
   opAt 2182 .MUL,
   opAt 2183 (.Dup ⟨0, by decide⟩),
   opAt 2184 (.Dup ⟨2, by decide⟩),
   opAt 2185 .MUL,
   pushAt 2186 1 2,
   opAt 2187 .SUB,
   opAt 2188 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2189 (.Dup ⟨0, by decide⟩),
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
   opAt 2200 .MUL,
   opAt 2201 (.Dup ⟨0, by decide⟩),
   opAt 2202 (.Dup ⟨2, by decide⟩),
   opAt 2203 .MUL,
   pushAt 2204 1 2,
   opAt 2205 .SUB,
   opAt 2206 .MUL,
   pushAt 2207 2 1664,
   opAt 2208 .MSTORE,
   opAt 2209 .POP,
   opAt 2210 .POP,
   opAt 2211 .POP,
   opAt 2212 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2244 .JUMPDEST,
   opAt 2245 (.Dup ⟨0, by decide⟩),
   opAt 2246 .ISZERO,
   pushAt 2247 2 3488,
   opAt 2248 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2249 (.Dup ⟨1, by decide⟩),
   pushAt 2250 2 2112,
   pushAt 2251 2 2080,
   opAt 2252 .MCOPY,
   pushAt 2253 0 0,
   pushAt 2254 2 2784,
   opAt 2255 .MLOAD,
   opAt 2256 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2257 2 2080,
   opAt 2258 .MLOAD,
   pushAt 2259 2 1536,
   opAt 2260 .MLOAD,
   opAt 2261 (.Dup ⟨1, by decide⟩),
   opAt 2262 .DIV,
   opAt 2263 (.Swap ⟨0, by decide⟩),
   pushAt 2264 2 1600,
   opAt 2265 .MLOAD,
   opAt 2266 .MUL,
   pushAt 2267 2 1536,
   opAt 2268 .MLOAD,
   pushAt 2269 2 2112,
   opAt 2270 .MLOAD,
   opAt 2271 .DIV,
   opAt 2272 .ADD,
   pushAt 2273 2 1568,
   opAt 2274 .MLOAD,
   opAt 2275 (.Dup ⟨0, by decide⟩),
   pushAt 2276 2 1632,
   opAt 2277 .MLOAD,
   opAt 2278 (.Dup ⟨4, by decide⟩),
   opAt 2279 .MULMOD,
   opAt 2280 (.Dup ⟨2, by decide⟩),
   opAt 2281 .ADDMOD,
   opAt 2282 (.Swap ⟨0, by decide⟩),
   opAt 2283 .SUB,
   pushAt 2284 2 1664,
   opAt 2285 .MLOAD,
   opAt 2286 .MUL,
   opAt 2287 (.Dup ⟨0, by decide⟩),
   pushAt 2288 0 0,
   opAt 2289 .MLOAD,
   opAt 2290 .MUL,
   pushAt 2291 2 2112,
   opAt 2292 .MLOAD,
   opAt 2293 .SUB,
   pushAt 2294 1 32,
   opAt 2295 .MLOAD,
   pushAt 2296 1 128,
   opAt 2297 .SHR,
   opAt 2298 (.Dup ⟨2, by decide⟩),
   pushAt 2299 1 128,
   opAt 2300 .SHR,
   opAt 2301 .MUL,
   opAt 2302 .GT,
   opAt 2303 (.Swap ⟨0, by decide⟩),
   opAt 2304 .SUB,
   opAt 2305 (.Swap ⟨0, by decide⟩),
   pushAt 2306 2 1568,
   opAt 2307 .MLOAD,
   opAt 2308 .GT,
   opAt 2309 .ISZERO,
   pushAt 2310 0 0,
   opAt 2311 .SUB,
   opAt 2312 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2313 0 0,
   pushAt 2314 1 31,
   opAt 2315 .NOT,
   pushAt 2316 0 0,
   opAt 2317 .NOT,
   pushAt 2318 2 2784,
   opAt 2319 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2323 .JUMPDEST,
   pushAt 2324 2 832,
   opAt 2325 (.Dup ⟨1, by decide⟩),
   opAt 2326 .SUB,
   opAt 2327 .MLOAD,
   opAt 2328 (.Dup ⟨2, by decide⟩),
   opAt 2329 (.Dup ⟨6, by decide⟩),
   opAt 2330 (.Dup ⟨2, by decide⟩),
   opAt 2331 .MUL,
   opAt 2332 (.Swap ⟨1, by decide⟩),
   opAt 2333 (.Dup ⟨7, by decide⟩),
   opAt 2334 .MULMOD,
   opAt 2335 (.Dup ⟨1, by decide⟩),
   opAt 2336 (.Dup ⟨1, by decide⟩),
   opAt 2337 .LT,
   opAt 2338 .SUB,
   opAt 2339 (.Dup ⟨5, by decide⟩),
   opAt 2340 (.Dup ⟨2, by decide⟩),
   opAt 2341 .ADD,
   opAt 2342 (.Dup ⟨0, by decide⟩),
   opAt 2343 (.Swap ⟨6, by decide⟩),
   opAt 2344 .GT,
   opAt 2345 .SUB,
   opAt 2346 .SUB,
   opAt 2347 (.Dup ⟨4, by decide⟩),
   opAt 2348 (.Dup ⟨2, by decide⟩),
   opAt 2349 .MLOAD,
   opAt 2350 .ADD,
   opAt 2351 (.Dup ⟨0, by decide⟩),
   opAt 2352 (.Swap ⟨5, by decide⟩),
   opAt 2353 .GT,
   opAt 2354 .ADD,
   opAt 2355 (.Swap ⟨3, by decide⟩),
   opAt 2356 (.Dup ⟨1, by decide⟩),
   opAt 2357 .MSTORE,
   opAt 2358 (.Dup ⟨2, by decide⟩),
   opAt 2359 .ADD,
   pushAt 2471 2 2080,
   opAt 2472 (.Dup ⟨1, by decide⟩),
   opAt 2473 .GT,
   pushAt 2474 2 3139,
   opAt 2475 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2476 .POP,
   opAt 2477 .POP,
   opAt 2478 .POP,
   pushAt 2479 2 2080,
   opAt 2480 .MLOAD,
   opAt 2481 (.Dup ⟨1, by decide⟩),
   opAt 2482 .ADD,
   opAt 2483 (.Dup ⟨0, by decide⟩),
   opAt 2484 (.Swap ⟨1, by decide⟩),
   opAt 2485 .GT,
   opAt 2486 (.Dup ⟨1, by decide⟩),
   opAt 2487 (.Dup ⟨3, by decide⟩),
   opAt 2488 .GT,
   opAt 2489 .GT,
   opAt 2490 (.Swap ⟨1, by decide⟩),
   opAt 2491 (.Swap ⟨0, by decide⟩),
   opAt 2492 .SUB,
   opAt 2493 (.Dup ⟨0, by decide⟩),
   pushAt 2494 2 2080,
   opAt 2495 .MSTORE,
   opAt 2496 (.Dup ⟨1, by decide⟩),
   opAt 2497 .OR,
   pushAt 2498 2 3344,
   opAt 2499 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2506 .JUMPDEST,
   opAt 2507 .ISZERO,
   pushAt 2508 2 3429,
   opAt 2509 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2510 .JUMPDEST,
   pushAt 2511 0 0,
   pushAt 2512 2 2784,
   opAt 2513 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2514 .JUMPDEST,
   opAt 2515 (.Dup ⟨0, by decide⟩),
   opAt 2516 .MLOAD,
   opAt 2517 (.Dup ⟨1, by decide⟩),
   pushAt 2518 2 2112,
   opAt 2519 (.Swap ⟨0, by decide⟩),
   opAt 2520 .SUB,
   opAt 2521 .MLOAD,
   opAt 2522 (.Dup ⟨1, by decide⟩),
   opAt 2523 .ADD,
   opAt 2524 (.Dup ⟨0, by decide⟩),
   opAt 2525 (.Dup ⟨2, by decide⟩),
   opAt 2526 .GT,
   opAt 2527 (.Swap ⟨1, by decide⟩),
   opAt 2528 .POP,
   opAt 2529 (.Dup ⟨3, by decide⟩),
   opAt 2530 .ADD,
   opAt 2531 (.Dup ⟨0, by decide⟩),
   opAt 2532 (.Dup ⟨4, by decide⟩),
   opAt 2533 .GT,
   opAt 2534 (.Swap ⟨3, by decide⟩),
   opAt 2535 .POP,
   opAt 2536 (.Dup ⟨2, by decide⟩),
   opAt 2537 .MSTORE,
   opAt 2538 (.Swap ⟨0, by decide⟩),
   opAt 2539 (.Swap ⟨1, by decide⟩),
   opAt 2540 .OR,
   opAt 2541 (.Swap ⟨0, by decide⟩),
   pushAt 2542 1 31,
   opAt 2543 .NOT,
   opAt 2544 .ADD,
   pushAt 2545 2 2111,
   opAt 2546 (.Dup ⟨1, by decide⟩),
   opAt 2547 .GT,
   pushAt 2548 2 3356,
   opAt 2549 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2550 .POP,
   pushAt 2551 2 2080,
   opAt 2552 .MLOAD,
   opAt 2553 (.Dup ⟨1, by decide⟩),
   opAt 2554 .ADD,
   opAt 2555 (.Dup ⟨0, by decide⟩),
   pushAt 2556 2 2080,
   opAt 2557 .MSTORE,
   opAt 2558 .LT,
   opAt 2559 .ISZERO,
   pushAt 2560 2 3350,
   opAt 2561 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2562 .JUMPDEST,
   pushAt 2563 2 2080,
   opAt 2564 .MLOAD,
   opAt 2565 (.Dup ⟨0, by decide⟩),
   opAt 2566 .ISZERO,
   pushAt 2567 2 3334,
   opAt 2568 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2562 .JUMPDEST,
   pushAt 2563 2 2080,
   opAt 2564 .MLOAD,
   opAt 2565 (.Dup ⟨0, by decide⟩),
   opAt 2566 .ISZERO,
   pushAt 2567 2 3334,
   opAt 2568 .JUMPI,
   opAt 2569 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2570 .JUMPDEST,
   pushAt 2571 0 0,
   pushAt 2572 2 2784,
   opAt 2573 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2574 .JUMPDEST,
   opAt 2575 (.Dup ⟨0, by decide⟩),
   opAt 2576 .MLOAD,
   pushAt 2577 2 2112,
   opAt 2578 (.Dup ⟨2, by decide⟩),
   opAt 2579 .SUB,
   opAt 2580 .MLOAD,
   opAt 2581 (.Dup ⟨1, by decide⟩),
   opAt 2582 (.Dup ⟨1, by decide⟩),
   opAt 2583 .GT,
   opAt 2584 (.Swap ⟨1, by decide⟩),
   opAt 2585 .SUB,
   opAt 2586 (.Dup ⟨3, by decide⟩),
   opAt 2587 (.Dup ⟨1, by decide⟩),
   opAt 2588 .LT,
   opAt 2589 (.Swap ⟨0, by decide⟩),
   opAt 2590 (.Dup ⟨4, by decide⟩),
   opAt 2591 (.Swap ⟨0, by decide⟩),
   opAt 2592 .SUB,
   opAt 2593 (.Dup ⟨3, by decide⟩),
   opAt 2594 .MSTORE,
   opAt 2595 .OR,
   opAt 2596 (.Swap ⟨1, by decide⟩),
   opAt 2597 .POP,
   pushAt 2598 1 31,
   opAt 2599 .NOT,
   opAt 2600 .ADD,
   pushAt 2601 2 2111,
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 .GT,
   pushAt 2604 2 3435,
   opAt 2605 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2606 .POP,
   pushAt 2607 2 2080,
   opAt 2608 .MLOAD,
   opAt 2609 .SUB,
   pushAt 2610 2 2080,
   opAt 2611 .MSTORE,
   pushAt 2612 2 3417,
   opAt 2613 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2500 .JUMPDEST,
   opAt 2501 .NOT,
   opAt 2502 .ADD,
   pushAt 2503 2 3024,
   pushAt 2504 2 4521,
   opAt 2505 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2634 (.Dup ⟨0, by decide⟩),
   pushAt 2635 2 2112,
   pushAt 2636 2 512,
   opAt 2637 .MCOPY,
   opAt 2638 (.Dup ⟨0, by decide⟩),
   pushAt 2639 2 1280,
   pushAt 2640 2 1024,
   opAt 2641 .MCOPY,
   pushAt 2642 2 2631,
   opAt 2643 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2788 = true :=
  Artifact.isValidJumpDest_index 2073 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2822 = true :=
  Artifact.isValidJumpDest_index 2095 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2839 = true :=
  Artifact.isValidJumpDest_index 2103 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2854 = true :=
  Artifact.isValidJumpDest_index 2111 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3024 = true :=
  Artifact.isValidJumpDest_index 2244 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3139 = true :=
  Artifact.isValidJumpDest_index 2323 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3350 = true :=
  Artifact.isValidJumpDest_index 2510 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3356 = true :=
  Artifact.isValidJumpDest_index 2514 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3417 = true :=
  Artifact.isValidJumpDest_index 2562 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3435 = true :=
  Artifact.isValidJumpDest_index 2574 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3344 = true :=
  Artifact.isValidJumpDest_index 2506 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3429 = true :=
  Artifact.isValidJumpDest_index 2570 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3334 = true :=
  Artifact.isValidJumpDest_index 2500 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3488 = true :=
  Artifact.isValidJumpDest_index 2614 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
