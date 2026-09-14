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
  [opAt 2078 .JUMPDEST,
   opAt 2079 (.Dup ⟨0, by decide⟩),
   opAt 2080 (.Dup ⟨3, by decide⟩),
   opAt 2081 .EQ,
   pushAt 2082 0 0,
   opAt 2083 .MLOAD,
   pushAt 2084 1 255,
   opAt 2085 .SHR,
   opAt 2086 .AND,
   opAt 2087 .ISZERO,
   pushAt 2088 2 2831,
   opAt 2089 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2090 (.Dup ⟨0, by decide⟩),
   pushAt 2091 1 96,
   pushAt 2092 2 2112,
   opAt 2093 .CALLDATACOPY,
   pushAt 2094 0 0,
   pushAt 2095 2 2080,
   opAt 2096 .MSTORE,
   pushAt 2097 2 2848,
   pushAt 2098 2 512,
   pushAt 2099 2 4330,
   opAt 2100 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2101 .JUMPDEST,
   pushAt 2102 1 1,
   pushAt 2103 2 1024,
   opAt 2104 .MSTORE,
   pushAt 2105 2 880,
   pushAt 2106 2 1024,
   pushAt 2107 2 1657,
   opAt 2108 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2114 1 1, pushAt 2115 2 2752, opAt 2116 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2138 .POP,
   opAt 2139 .POP,
   pushAt 2140 0 0,
   opAt 2141 .MLOAD,
   opAt 2142 (.Dup ⟨0, by decide⟩),
   pushAt 2143 0 0,
   opAt 2144 .SUB,
   opAt 2145 (.Dup ⟨1, by decide⟩),
   opAt 2146 .AND,
   opAt 2147 (.Dup ⟨0, by decide⟩),
   pushAt 2148 2 1536,
   opAt 2149 .MSTORE,
   opAt 2150 (.Dup ⟨0, by decide⟩),
   opAt 2151 (.Dup ⟨2, by decide⟩),
   opAt 2152 .DIV,
   opAt 2153 (.Dup ⟨0, by decide⟩),
   pushAt 2154 2 1568,
   opAt 2155 .MSTORE,
   opAt 2156 (.Dup ⟨1, by decide⟩),
   opAt 2157 (.Dup ⟨0, by decide⟩),
   pushAt 2158 0 0,
   opAt 2159 .SUB,
   opAt 2160 .DIV,
   pushAt 2161 1 1,
   opAt 2162 .ADD,
   pushAt 2163 2 1600,
   opAt 2164 .MSTORE,
   opAt 2165 (.Dup ⟨0, by decide⟩),
   opAt 2166 (.Dup ⟨0, by decide⟩),
   pushAt 2167 0 0,
   opAt 2168 .SUB,
   opAt 2169 .MOD,
   pushAt 2170 2 1632,
   opAt 2171 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2172 (.Dup ⟨0, by decide⟩),
   pushAt 2173 1 3,
   opAt 2174 .MUL,
   pushAt 2175 1 2,
   opAt 2176 .XOR,
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
   opAt 2188 .MUL,
   opAt 2189 (.Dup ⟨0, by decide⟩),
   opAt 2190 (.Dup ⟨2, by decide⟩),
   opAt 2191 .MUL,
   pushAt 2192 1 2,
   opAt 2193 .SUB,
   opAt 2194 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2195 (.Dup ⟨0, by decide⟩),
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
   opAt 2207 (.Dup ⟨0, by decide⟩),
   opAt 2208 (.Dup ⟨2, by decide⟩),
   opAt 2209 .MUL,
   pushAt 2210 1 2,
   opAt 2211 .SUB,
   opAt 2212 .MUL,
   pushAt 2213 2 1664,
   opAt 2214 .MSTORE,
   opAt 2215 .POP,
   opAt 2216 .POP,
   opAt 2217 .POP,
   opAt 2218 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2250 .JUMPDEST,
   opAt 2251 (.Dup ⟨0, by decide⟩),
   opAt 2252 .ISZERO,
   pushAt 2253 2 3502,
   opAt 2254 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2255 (.Dup ⟨1, by decide⟩),
   pushAt 2256 2 512,
   pushAt 2257 2 2080,
   opAt 2258 .MCOPY,
   pushAt 2259 0 0,
   pushAt 2260 2 2784,
   opAt 2261 .MLOAD,
   opAt 2262 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2263 2 512,
   opAt 2264 .MLOAD,
   pushAt 2265 2 1536,
   opAt 2266 .MLOAD,
   opAt 2267 (.Dup ⟨1, by decide⟩),
   opAt 2268 .DIV,
   opAt 2269 (.Swap ⟨0, by decide⟩),
   pushAt 2270 2 1600,
   opAt 2271 .MLOAD,
   opAt 2272 .MUL,
   pushAt 2273 2 1536,
   opAt 2274 .MLOAD,
   pushAt 2275 2 544,
   opAt 2276 .MLOAD,
   opAt 2277 .DIV,
   opAt 2278 .ADD,
   pushAt 2279 2 1568,
   opAt 2280 .MLOAD,
   opAt 2281 (.Dup ⟨0, by decide⟩),
   pushAt 2282 2 1632,
   opAt 2283 .MLOAD,
   opAt 2284 (.Dup ⟨4, by decide⟩),
   opAt 2285 .MULMOD,
   opAt 2286 (.Dup ⟨2, by decide⟩),
   opAt 2287 .ADDMOD,
   opAt 2288 (.Swap ⟨0, by decide⟩),
   opAt 2289 .SUB,
   pushAt 2290 2 1664,
   opAt 2291 .MLOAD,
   opAt 2292 .MUL,
   opAt 2293 (.Dup ⟨0, by decide⟩),
   pushAt 2294 0 0,
   opAt 2295 .MLOAD,
   opAt 2296 .MUL,
   pushAt 2297 2 544,
   opAt 2298 .MLOAD,
   opAt 2299 .SUB,
   pushAt 2300 1 32,
   opAt 2301 .MLOAD,
   pushAt 2302 1 128,
   opAt 2303 .SHR,
   opAt 2304 (.Dup ⟨2, by decide⟩),
   pushAt 2305 1 128,
   opAt 2306 .SHR,
   opAt 2307 .MUL,
   opAt 2308 .GT,
   opAt 2309 (.Swap ⟨0, by decide⟩),
   opAt 2310 .SUB,
   opAt 2311 (.Swap ⟨0, by decide⟩),
   pushAt 2312 2 1568,
   opAt 2313 .MLOAD,
   opAt 2314 .GT,
   opAt 2315 .ISZERO,
   pushAt 2316 0 0,
   opAt 2317 .SUB,
   opAt 2318 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2319 0 0,
   pushAt 2320 1 31,
   opAt 2321 .NOT,
   pushAt 2322 0 0,
   opAt 2323 .NOT,
   pushAt 2324 2 2784,
   opAt 2325 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2331 .JUMPDEST,
   pushAt 2332 2 832,
   opAt 2333 (.Dup ⟨1, by decide⟩),
   opAt 2334 .SUB,
   opAt 2335 .MLOAD,
   opAt 2336 (.Dup ⟨2, by decide⟩),
   opAt 2337 (.Dup ⟨6, by decide⟩),
   opAt 2338 (.Dup ⟨2, by decide⟩),
   opAt 2339 .MUL,
   opAt 2340 (.Swap ⟨1, by decide⟩),
   opAt 2341 (.Dup ⟨7, by decide⟩),
   opAt 2342 .MULMOD,
   opAt 2343 (.Dup ⟨1, by decide⟩),
   opAt 2344 (.Dup ⟨1, by decide⟩),
   opAt 2345 .LT,
   opAt 2346 .SUB,
   opAt 2347 (.Dup ⟨5, by decide⟩),
   opAt 2348 (.Dup ⟨2, by decide⟩),
   opAt 2349 .ADD,
   opAt 2350 (.Dup ⟨0, by decide⟩),
   opAt 2351 (.Swap ⟨6, by decide⟩),
   opAt 2352 .GT,
   opAt 2353 .SUB,
   opAt 2354 .SUB,
   opAt 2355 (.Dup ⟨4, by decide⟩),
   opAt 2356 (.Dup ⟨2, by decide⟩),
   opAt 2357 .MLOAD,
   opAt 2358 .ADD,
   opAt 2359 (.Dup ⟨0, by decide⟩),
   opAt 2360 (.Swap ⟨5, by decide⟩),
   opAt 2361 .GT,
   opAt 2362 .ADD,
   opAt 2363 (.Swap ⟨3, by decide⟩),
   opAt 2364 (.Dup ⟨1, by decide⟩),
   opAt 2365 .MSTORE,
   opAt 2366 (.Dup ⟨2, by decide⟩),
   opAt 2367 .ADD,
   pushAt 2479 2 2080,
   opAt 2480 (.Dup ⟨1, by decide⟩),
   opAt 2481 .GT,
   pushAt 2482 2 3150,
   opAt 2483 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2484 .POP,
   opAt 2485 .POP,
   opAt 2486 .POP,
   pushAt 2487 2 2080,
   opAt 2488 .MLOAD,
   opAt 2489 (.Dup ⟨1, by decide⟩),
   opAt 2490 .ADD,
   opAt 2491 (.Dup ⟨0, by decide⟩),
   opAt 2492 (.Swap ⟨1, by decide⟩),
   opAt 2493 .GT,
   opAt 2494 (.Dup ⟨1, by decide⟩),
   opAt 2495 (.Dup ⟨3, by decide⟩),
   opAt 2496 .GT,
   opAt 2497 .GT,
   opAt 2498 (.Swap ⟨1, by decide⟩),
   opAt 2499 (.Swap ⟨0, by decide⟩),
   opAt 2500 .SUB,
   opAt 2501 (.Dup ⟨0, by decide⟩),
   pushAt 2502 2 2080,
   opAt 2503 .MSTORE,
   opAt 2504 (.Dup ⟨1, by decide⟩),
   opAt 2505 .OR,
   pushAt 2506 2 3358,
   opAt 2507 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2515 .JUMPDEST,
   opAt 2516 .ISZERO,
   pushAt 2517 2 3443,
   opAt 2518 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2519 .JUMPDEST,
   pushAt 2520 0 0,
   pushAt 2521 2 2784,
   opAt 2522 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2523 .JUMPDEST,
   opAt 2524 (.Dup ⟨0, by decide⟩),
   opAt 2525 .MLOAD,
   opAt 2526 (.Dup ⟨1, by decide⟩),
   pushAt 2527 2 2112,
   opAt 2528 (.Swap ⟨0, by decide⟩),
   opAt 2529 .SUB,
   opAt 2530 .MLOAD,
   opAt 2531 (.Dup ⟨1, by decide⟩),
   opAt 2532 .ADD,
   opAt 2533 (.Dup ⟨0, by decide⟩),
   opAt 2534 (.Dup ⟨2, by decide⟩),
   opAt 2535 .GT,
   opAt 2536 (.Swap ⟨1, by decide⟩),
   opAt 2537 .POP,
   opAt 2538 (.Dup ⟨3, by decide⟩),
   opAt 2539 .ADD,
   opAt 2540 (.Dup ⟨0, by decide⟩),
   opAt 2541 (.Dup ⟨4, by decide⟩),
   opAt 2542 .GT,
   opAt 2543 (.Swap ⟨3, by decide⟩),
   opAt 2544 .POP,
   opAt 2545 (.Dup ⟨2, by decide⟩),
   opAt 2546 .MSTORE,
   opAt 2547 (.Swap ⟨0, by decide⟩),
   opAt 2548 (.Swap ⟨1, by decide⟩),
   opAt 2549 .OR,
   opAt 2550 (.Swap ⟨0, by decide⟩),
   pushAt 2551 1 31,
   opAt 2552 .NOT,
   opAt 2553 .ADD,
   pushAt 2554 2 2111,
   opAt 2555 (.Dup ⟨1, by decide⟩),
   opAt 2556 .GT,
   pushAt 2557 2 3370,
   opAt 2558 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2559 .POP,
   pushAt 2560 2 2080,
   opAt 2561 .MLOAD,
   opAt 2562 (.Dup ⟨1, by decide⟩),
   opAt 2563 .ADD,
   opAt 2564 (.Dup ⟨0, by decide⟩),
   pushAt 2565 2 2080,
   opAt 2566 .MSTORE,
   opAt 2567 .LT,
   opAt 2568 .ISZERO,
   pushAt 2569 2 3364,
   opAt 2570 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2571 .JUMPDEST,
   pushAt 2572 2 2080,
   opAt 2573 .MLOAD,
   opAt 2574 (.Dup ⟨0, by decide⟩),
   opAt 2575 .ISZERO,
   pushAt 2576 2 3345,
   opAt 2577 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2571 .JUMPDEST,
   pushAt 2572 2 2080,
   opAt 2573 .MLOAD,
   opAt 2574 (.Dup ⟨0, by decide⟩),
   opAt 2575 .ISZERO,
   pushAt 2576 2 3345,
   opAt 2577 .JUMPI,
   opAt 2578 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .JUMPDEST,
   pushAt 2580 0 0,
   pushAt 2581 2 2784,
   opAt 2582 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .JUMPDEST,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   opAt 2585 .MLOAD,
   pushAt 2586 2 2112,
   opAt 2587 (.Dup ⟨2, by decide⟩),
   opAt 2588 .SUB,
   opAt 2589 .MLOAD,
   opAt 2590 (.Dup ⟨1, by decide⟩),
   opAt 2591 (.Dup ⟨1, by decide⟩),
   opAt 2592 .GT,
   opAt 2593 (.Swap ⟨1, by decide⟩),
   opAt 2594 .SUB,
   opAt 2595 (.Dup ⟨3, by decide⟩),
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 .LT,
   opAt 2598 (.Swap ⟨0, by decide⟩),
   opAt 2599 (.Dup ⟨4, by decide⟩),
   opAt 2600 (.Swap ⟨0, by decide⟩),
   opAt 2601 .SUB,
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 .MSTORE,
   opAt 2604 .OR,
   opAt 2605 (.Swap ⟨1, by decide⟩),
   opAt 2606 .POP,
   pushAt 2607 1 31,
   opAt 2608 .NOT,
   opAt 2609 .ADD,
   pushAt 2610 2 2111,
   opAt 2611 (.Dup ⟨1, by decide⟩),
   opAt 2612 .GT,
   pushAt 2613 2 3449,
   opAt 2614 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2615 .POP,
   pushAt 2616 2 2080,
   opAt 2617 .MLOAD,
   opAt 2618 .SUB,
   pushAt 2619 2 2080,
   opAt 2620 .MSTORE,
   pushAt 2621 2 3431,
   opAt 2622 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2508 .JUMPDEST,
   opAt 2509 .NOT,
   opAt 2510 .ADD,
   pushAt 2511 2 3033,
   pushAt 2512 2 512,
   pushAt 2513 2 4330,
   opAt 2514 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2643 2 2688,
   opAt 2644 .MLOAD,
   pushAt 2645 2 1280,
   pushAt 2646 2 1024,
   opAt 2647 .MCOPY,
   pushAt 2648 2 2637,
   opAt 2649 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2794 = true :=
  Artifact.isValidJumpDest_index 2078 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2831 = true :=
  Artifact.isValidJumpDest_index 2101 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2848 = true :=
  Artifact.isValidJumpDest_index 2109 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2863 = true :=
  Artifact.isValidJumpDest_index 2117 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3033 = true :=
  Artifact.isValidJumpDest_index 2250 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3150 = true :=
  Artifact.isValidJumpDest_index 2331 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3364 = true :=
  Artifact.isValidJumpDest_index 2519 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3370 = true :=
  Artifact.isValidJumpDest_index 2523 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3431 = true :=
  Artifact.isValidJumpDest_index 2571 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3449 = true :=
  Artifact.isValidJumpDest_index 2583 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3358 = true :=
  Artifact.isValidJumpDest_index 2515 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3443 = true :=
  Artifact.isValidJumpDest_index 2579 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3345 = true :=
  Artifact.isValidJumpDest_index 2508 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3502 = true :=
  Artifact.isValidJumpDest_index 2623 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
