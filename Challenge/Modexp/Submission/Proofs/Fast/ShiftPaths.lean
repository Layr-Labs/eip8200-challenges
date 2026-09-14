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
  [opAt 2077 .JUMPDEST,
   opAt 2078 (.Dup ⟨0, by decide⟩),
   opAt 2079 (.Dup ⟨3, by decide⟩),
   opAt 2080 .EQ,
   pushAt 2081 0 0,
   opAt 2082 .MLOAD,
   pushAt 2083 1 255,
   opAt 2084 .SHR,
   opAt 2085 .AND,
   opAt 2086 .ISZERO,
   pushAt 2087 2 2827,
   opAt 2088 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2089 (.Dup ⟨0, by decide⟩),
   pushAt 2090 1 96,
   pushAt 2091 2 2112,
   opAt 2092 .CALLDATACOPY,
   pushAt 2093 0 0,
   pushAt 2094 2 2080,
   opAt 2095 .MSTORE,
   pushAt 2096 2 2844,
   pushAt 2097 2 4486,
   opAt 2098 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2099 .JUMPDEST,
   pushAt 2100 1 1,
   pushAt 2101 2 1024,
   opAt 2102 .MSTORE,
   pushAt 2103 2 880,
   pushAt 2104 2 1024,
   pushAt 2105 2 1658,
   opAt 2106 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2112 1 1,
   pushAt 2113 2 2752,
   opAt 2114 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2136 .POP,
   opAt 2137 .POP,
   pushAt 2138 0 0,
   opAt 2139 .MLOAD,
   opAt 2140 (.Dup ⟨0, by decide⟩),
   pushAt 2141 0 0,
   opAt 2142 .SUB,
   opAt 2143 (.Dup ⟨1, by decide⟩),
   opAt 2144 .AND,
   opAt 2145 (.Dup ⟨0, by decide⟩),
   pushAt 2146 2 1536,
   opAt 2147 .MSTORE,
   opAt 2148 (.Dup ⟨0, by decide⟩),
   opAt 2149 (.Dup ⟨2, by decide⟩),
   opAt 2150 .DIV,
   opAt 2151 (.Dup ⟨0, by decide⟩),
   pushAt 2152 2 1568,
   opAt 2153 .MSTORE,
   opAt 2154 (.Dup ⟨1, by decide⟩),
   opAt 2155 (.Dup ⟨0, by decide⟩),
   pushAt 2156 0 0,
   opAt 2157 .SUB,
   opAt 2158 .DIV,
   pushAt 2159 1 1,
   opAt 2160 .ADD,
   pushAt 2161 2 1600,
   opAt 2162 .MSTORE,
   opAt 2163 (.Dup ⟨0, by decide⟩),
   opAt 2164 (.Dup ⟨0, by decide⟩),
   pushAt 2165 0 0,
   opAt 2166 .SUB,
   opAt 2167 .MOD,
   pushAt 2168 2 1632,
   opAt 2169 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2170 (.Dup ⟨0, by decide⟩),
   pushAt 2171 1 3,
   opAt 2172 .MUL,
   pushAt 2173 1 2,
   opAt 2174 .XOR,
   opAt 2175 (.Dup ⟨0, by decide⟩),
   opAt 2176 (.Dup ⟨2, by decide⟩),
   opAt 2177 .MUL,
   pushAt 2178 1 2,
   opAt 2179 .SUB,
   opAt 2180 .MUL,
   opAt 2181 (.Dup ⟨0, by decide⟩),
   opAt 2182 (.Dup ⟨2, by decide⟩),
   opAt 2183 .MUL,
   pushAt 2184 1 2,
   opAt 2185 .SUB,
   opAt 2186 .MUL,
   opAt 2187 (.Dup ⟨0, by decide⟩),
   opAt 2188 (.Dup ⟨2, by decide⟩),
   opAt 2189 .MUL,
   pushAt 2190 1 2,
   opAt 2191 .SUB,
   opAt 2192 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2193 (.Dup ⟨0, by decide⟩),
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
   opAt 2204 .MUL,
   opAt 2205 (.Dup ⟨0, by decide⟩),
   opAt 2206 (.Dup ⟨2, by decide⟩),
   opAt 2207 .MUL,
   pushAt 2208 1 2,
   opAt 2209 .SUB,
   opAt 2210 .MUL,
   pushAt 2211 2 1664,
   opAt 2212 .MSTORE,
   opAt 2213 .POP,
   opAt 2214 .POP,
   opAt 2215 .POP,
   opAt 2216 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2248 .JUMPDEST,
   opAt 2249 (.Dup ⟨0, by decide⟩),
   opAt 2250 .ISZERO,
   pushAt 2251 2 3493,
   opAt 2252 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2253 (.Dup ⟨1, by decide⟩),
   pushAt 2254 2 2112,
   pushAt 2255 2 2080,
   opAt 2256 .MCOPY,
   pushAt 2257 0 0,
   pushAt 2258 2 2784,
   opAt 2259 .MLOAD,
   opAt 2260 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2261 2 2080,
   opAt 2262 .MLOAD,
   pushAt 2263 2 1536,
   opAt 2264 .MLOAD,
   opAt 2265 (.Dup ⟨1, by decide⟩),
   opAt 2266 .DIV,
   opAt 2267 (.Swap ⟨0, by decide⟩),
   pushAt 2268 2 1600,
   opAt 2269 .MLOAD,
   opAt 2270 .MUL,
   pushAt 2271 2 1536,
   opAt 2272 .MLOAD,
   pushAt 2273 2 2112,
   opAt 2274 .MLOAD,
   opAt 2275 .DIV,
   opAt 2276 .ADD,
   pushAt 2277 2 1568,
   opAt 2278 .MLOAD,
   opAt 2279 (.Dup ⟨0, by decide⟩),
   pushAt 2280 2 1632,
   opAt 2281 .MLOAD,
   opAt 2282 (.Dup ⟨4, by decide⟩),
   opAt 2283 .MULMOD,
   opAt 2284 (.Dup ⟨2, by decide⟩),
   opAt 2285 .ADDMOD,
   opAt 2286 (.Swap ⟨0, by decide⟩),
   opAt 2287 .SUB,
   pushAt 2288 2 1664,
   opAt 2289 .MLOAD,
   opAt 2290 .MUL,
   opAt 2291 (.Dup ⟨0, by decide⟩),
   pushAt 2292 0 0,
   opAt 2293 .MLOAD,
   opAt 2294 .MUL,
   pushAt 2295 2 2112,
   opAt 2296 .MLOAD,
   opAt 2297 .SUB,
   pushAt 2298 1 32,
   opAt 2299 .MLOAD,
   pushAt 2300 1 128,
   opAt 2301 .SHR,
   opAt 2302 (.Dup ⟨2, by decide⟩),
   pushAt 2303 1 128,
   opAt 2304 .SHR,
   opAt 2305 .MUL,
   opAt 2306 .GT,
   opAt 2307 (.Swap ⟨0, by decide⟩),
   opAt 2308 .SUB,
   opAt 2309 (.Swap ⟨0, by decide⟩),
   pushAt 2310 2 1568,
   opAt 2311 .MLOAD,
   opAt 2312 .GT,
   opAt 2313 .ISZERO,
   pushAt 2314 0 0,
   opAt 2315 .SUB,
   opAt 2316 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2317 0 0,
   pushAt 2318 1 31,
   opAt 2319 .NOT,
   pushAt 2320 0 0,
   opAt 2321 .NOT,
   pushAt 2322 2 2784,
   opAt 2323 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2327 .JUMPDEST,
   pushAt 2328 2 832,
   opAt 2329 (.Dup ⟨1, by decide⟩),
   opAt 2330 .SUB,
   opAt 2331 .MLOAD,
   opAt 2332 (.Dup ⟨2, by decide⟩),
   opAt 2333 (.Dup ⟨6, by decide⟩),
   opAt 2334 (.Dup ⟨2, by decide⟩),
   opAt 2335 .MUL,
   opAt 2336 (.Swap ⟨1, by decide⟩),
   opAt 2337 (.Dup ⟨7, by decide⟩),
   opAt 2338 .MULMOD,
   opAt 2339 (.Dup ⟨1, by decide⟩),
   opAt 2340 (.Dup ⟨1, by decide⟩),
   opAt 2341 .LT,
   opAt 2342 .SUB,
   opAt 2343 (.Dup ⟨5, by decide⟩),
   opAt 2344 (.Dup ⟨2, by decide⟩),
   opAt 2345 .ADD,
   opAt 2346 (.Dup ⟨0, by decide⟩),
   opAt 2347 (.Swap ⟨6, by decide⟩),
   opAt 2348 .GT,
   opAt 2349 .SUB,
   opAt 2350 .SUB,
   opAt 2351 (.Dup ⟨4, by decide⟩),
   opAt 2352 (.Dup ⟨2, by decide⟩),
   opAt 2353 .MLOAD,
   opAt 2354 .ADD,
   opAt 2355 (.Dup ⟨0, by decide⟩),
   opAt 2356 (.Swap ⟨5, by decide⟩),
   opAt 2357 .GT,
   opAt 2358 .ADD,
   opAt 2359 (.Swap ⟨3, by decide⟩),
   opAt 2360 (.Dup ⟨1, by decide⟩),
   opAt 2361 .MSTORE,
   opAt 2362 (.Dup ⟨2, by decide⟩),
   opAt 2363 .ADD,
   pushAt 2475 2 2080,
   opAt 2476 (.Dup ⟨1, by decide⟩),
   opAt 2477 .GT,
   pushAt 2478 2 3144,
   opAt 2479 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2480 .POP,
   opAt 2481 .POP,
   opAt 2482 .POP,
   pushAt 2483 2 2080,
   opAt 2484 .MLOAD,
   opAt 2485 (.Dup ⟨1, by decide⟩),
   opAt 2486 .ADD,
   opAt 2487 (.Dup ⟨0, by decide⟩),
   opAt 2488 (.Swap ⟨1, by decide⟩),
   opAt 2489 .GT,
   opAt 2490 (.Dup ⟨1, by decide⟩),
   opAt 2491 (.Dup ⟨3, by decide⟩),
   opAt 2492 .GT,
   opAt 2493 .GT,
   opAt 2494 (.Swap ⟨1, by decide⟩),
   opAt 2495 (.Swap ⟨0, by decide⟩),
   opAt 2496 .SUB,
   opAt 2497 (.Dup ⟨0, by decide⟩),
   pushAt 2498 2 2080,
   opAt 2499 .MSTORE,
   opAt 2500 (.Dup ⟨1, by decide⟩),
   opAt 2501 .OR,
   pushAt 2502 2 3349,
   opAt 2503 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2510 .JUMPDEST,
   opAt 2511 .ISZERO,
   pushAt 2512 2 3434,
   opAt 2513 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2514 .JUMPDEST,
   pushAt 2515 0 0,
   pushAt 2516 2 2784,
   opAt 2517 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2518 .JUMPDEST,
   opAt 2519 (.Dup ⟨0, by decide⟩),
   opAt 2520 .MLOAD,
   opAt 2521 (.Dup ⟨1, by decide⟩),
   pushAt 2522 2 2112,
   opAt 2523 (.Swap ⟨0, by decide⟩),
   opAt 2524 .SUB,
   opAt 2525 .MLOAD,
   opAt 2526 (.Dup ⟨1, by decide⟩),
   opAt 2527 .ADD,
   opAt 2528 (.Dup ⟨0, by decide⟩),
   opAt 2529 (.Dup ⟨2, by decide⟩),
   opAt 2530 .GT,
   opAt 2531 (.Swap ⟨1, by decide⟩),
   opAt 2532 .POP,
   opAt 2533 (.Dup ⟨3, by decide⟩),
   opAt 2534 .ADD,
   opAt 2535 (.Dup ⟨0, by decide⟩),
   opAt 2536 (.Dup ⟨4, by decide⟩),
   opAt 2537 .GT,
   opAt 2538 (.Swap ⟨3, by decide⟩),
   opAt 2539 .POP,
   opAt 2540 (.Dup ⟨2, by decide⟩),
   opAt 2541 .MSTORE,
   opAt 2542 (.Swap ⟨0, by decide⟩),
   opAt 2543 (.Swap ⟨1, by decide⟩),
   opAt 2544 .OR,
   opAt 2545 (.Swap ⟨0, by decide⟩),
   pushAt 2546 1 31,
   opAt 2547 .NOT,
   opAt 2548 .ADD,
   pushAt 2549 2 2111,
   opAt 2550 (.Dup ⟨1, by decide⟩),
   opAt 2551 .GT,
   pushAt 2552 2 3361,
   opAt 2553 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2554 .POP,
   pushAt 2555 2 2080,
   opAt 2556 .MLOAD,
   opAt 2557 (.Dup ⟨1, by decide⟩),
   opAt 2558 .ADD,
   opAt 2559 (.Dup ⟨0, by decide⟩),
   pushAt 2560 2 2080,
   opAt 2561 .MSTORE,
   opAt 2562 .LT,
   opAt 2563 .ISZERO,
   pushAt 2564 2 3355,
   opAt 2565 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2566 .JUMPDEST,
   pushAt 2567 2 2080,
   opAt 2568 .MLOAD,
   opAt 2569 (.Dup ⟨0, by decide⟩),
   opAt 2570 .ISZERO,
   pushAt 2571 2 3339,
   opAt 2572 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2566 .JUMPDEST,
   pushAt 2567 2 2080,
   opAt 2568 .MLOAD,
   opAt 2569 (.Dup ⟨0, by decide⟩),
   opAt 2570 .ISZERO,
   pushAt 2571 2 3339,
   opAt 2572 .JUMPI,
   opAt 2573 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2574 .JUMPDEST,
   pushAt 2575 0 0,
   pushAt 2576 2 2784,
   opAt 2577 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .JUMPDEST,
   opAt 2579 (.Dup ⟨0, by decide⟩),
   opAt 2580 .MLOAD,
   pushAt 2581 2 2112,
   opAt 2582 (.Dup ⟨2, by decide⟩),
   opAt 2583 .SUB,
   opAt 2584 .MLOAD,
   opAt 2585 (.Dup ⟨1, by decide⟩),
   opAt 2586 (.Dup ⟨1, by decide⟩),
   opAt 2587 .GT,
   opAt 2588 (.Swap ⟨1, by decide⟩),
   opAt 2589 .SUB,
   opAt 2590 (.Dup ⟨3, by decide⟩),
   opAt 2591 (.Dup ⟨1, by decide⟩),
   opAt 2592 .LT,
   opAt 2593 (.Swap ⟨0, by decide⟩),
   opAt 2594 (.Dup ⟨4, by decide⟩),
   opAt 2595 (.Swap ⟨0, by decide⟩),
   opAt 2596 .SUB,
   opAt 2597 (.Dup ⟨3, by decide⟩),
   opAt 2598 .MSTORE,
   opAt 2599 .OR,
   opAt 2600 (.Swap ⟨1, by decide⟩),
   opAt 2601 .POP,
   pushAt 2602 1 31,
   opAt 2603 .NOT,
   opAt 2604 .ADD,
   pushAt 2605 2 2111,
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 .GT,
   pushAt 2608 2 3440,
   opAt 2609 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2610 .POP,
   pushAt 2611 2 2080,
   opAt 2612 .MLOAD,
   opAt 2613 .SUB,
   pushAt 2614 2 2080,
   opAt 2615 .MSTORE,
   pushAt 2616 2 3422,
   opAt 2617 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2504 .JUMPDEST,
   opAt 2505 .NOT,
   opAt 2506 .ADD,
   pushAt 2507 2 3029,
   pushAt 2508 2 4486,
   opAt 2509 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2638 (.Dup ⟨0, by decide⟩),
   pushAt 2639 2 2112,
   pushAt 2640 2 512,
   opAt 2641 .MCOPY,
   opAt 2642 (.Dup ⟨0, by decide⟩),
   pushAt 2643 2 1280,
   pushAt 2644 2 1024,
   opAt 2645 .MCOPY,
   pushAt 2646 2 2636,
   opAt 2647 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2793 = true :=
  Artifact.isValidJumpDest_index 2077 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2827 = true :=
  Artifact.isValidJumpDest_index 2099 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2844 = true :=
  Artifact.isValidJumpDest_index 2107 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2859 = true :=
  Artifact.isValidJumpDest_index 2115 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3029 = true :=
  Artifact.isValidJumpDest_index 2248 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3144 = true :=
  Artifact.isValidJumpDest_index 2327 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3355 = true :=
  Artifact.isValidJumpDest_index 2514 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3361 = true :=
  Artifact.isValidJumpDest_index 2518 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3422 = true :=
  Artifact.isValidJumpDest_index 2566 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3440 = true :=
  Artifact.isValidJumpDest_index 2578 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3349 = true :=
  Artifact.isValidJumpDest_index 2510 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3434 = true :=
  Artifact.isValidJumpDest_index 2574 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3339 = true :=
  Artifact.isValidJumpDest_index 2504 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3493 = true :=
  Artifact.isValidJumpDest_index 2618 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
