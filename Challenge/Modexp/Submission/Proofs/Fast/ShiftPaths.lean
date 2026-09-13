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
  [opAt 2098 .JUMPDEST,
   opAt 2099 (.Dup ⟨0, by decide⟩),
   opAt 2100 (.Dup ⟨3, by decide⟩),
   opAt 2101 .EQ,
   pushAt 2102 0 0,
   opAt 2103 .MLOAD,
   pushAt 2104 1 255,
   opAt 2105 .SHR,
   opAt 2106 .AND,
   opAt 2107 .ISZERO,
   pushAt 2108 2 2884,
   opAt 2109 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2110 (.Dup ⟨0, by decide⟩),
   pushAt 2111 1 96,
   pushAt 2112 2 256,
   opAt 2113 .CALLDATACOPY,
   opAt 2114 (.Dup ⟨0, by decide⟩),
   pushAt 2115 1 96,
   pushAt 2116 2 2112,
   opAt 2117 .CALLDATACOPY,
   pushAt 2118 0 0,
   pushAt 2119 2 2080,
   opAt 2120 .MSTORE,
   pushAt 2121 2 2901,
   pushAt 2122 2 512,
   pushAt 2123 2 4337,
   opAt 2124 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2125 .JUMPDEST,
   pushAt 2126 1 1,
   pushAt 2127 2 1024,
   opAt 2128 .MSTORE,
   pushAt 2129 2 896,
   pushAt 2130 2 1024,
   pushAt 2131 2 1674,
   opAt 2132 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2133 .JUMPDEST,
   pushAt 2134 1 1,
   pushAt 2135 2 2752,
   opAt 2136 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2159 .JUMPDEST,
   opAt 2160 .POP,
   opAt 2161 .POP,
   pushAt 2162 0 0,
   opAt 2163 .MLOAD,
   opAt 2164 (.Dup ⟨0, by decide⟩),
   pushAt 2165 0 0,
   opAt 2166 .SUB,
   opAt 2167 (.Dup ⟨1, by decide⟩),
   opAt 2168 .AND,
   opAt 2169 (.Dup ⟨0, by decide⟩),
   pushAt 2170 2 1536,
   opAt 2171 .MSTORE,
   opAt 2172 (.Dup ⟨0, by decide⟩),
   opAt 2173 (.Dup ⟨2, by decide⟩),
   opAt 2174 .DIV,
   opAt 2175 (.Dup ⟨0, by decide⟩),
   pushAt 2176 2 1568,
   opAt 2177 .MSTORE,
   opAt 2178 (.Dup ⟨1, by decide⟩),
   pushAt 2179 0 0,
   opAt 2180 .SUB,
   opAt 2181 (.Dup ⟨2, by decide⟩),
   opAt 2182 (.Swap ⟨0, by decide⟩),
   opAt 2183 .DIV,
   pushAt 2184 1 1,
   opAt 2185 .ADD,
   pushAt 2186 2 1600,
   opAt 2187 .MSTORE,
   opAt 2188 (.Dup ⟨0, by decide⟩),
   pushAt 2189 0 0,
   opAt 2190 .SUB,
   opAt 2191 (.Dup ⟨1, by decide⟩),
   opAt 2192 (.Swap ⟨0, by decide⟩),
   opAt 2193 .MOD,
   pushAt 2194 2 1632,
   opAt 2195 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2196 (.Dup ⟨0, by decide⟩),
   pushAt 2197 1 2,
   opAt 2198 .SUB,
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
   opAt 2211 (.Dup ⟨0, by decide⟩),
   opAt 2212 (.Dup ⟨2, by decide⟩),
   opAt 2213 .MUL,
   pushAt 2214 1 2,
   opAt 2215 .SUB,
   opAt 2216 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2217 (.Dup ⟨0, by decide⟩),
   opAt 2218 (.Dup ⟨2, by decide⟩),
   opAt 2219 .MUL,
   pushAt 2220 1 2,
   opAt 2221 .SUB,
   opAt 2222 .MUL,
   opAt 2223 (.Dup ⟨0, by decide⟩),
   opAt 2224 (.Dup ⟨2, by decide⟩),
   opAt 2225 .MUL,
   pushAt 2226 1 2,
   opAt 2227 .SUB,
   opAt 2228 .MUL,
   opAt 2229 (.Dup ⟨0, by decide⟩),
   opAt 2230 (.Dup ⟨2, by decide⟩),
   opAt 2231 .MUL,
   pushAt 2232 1 2,
   opAt 2233 .SUB,
   opAt 2234 .MUL,
   opAt 2235 (.Dup ⟨0, by decide⟩),
   opAt 2236 (.Dup ⟨2, by decide⟩),
   opAt 2237 .MUL,
   pushAt 2238 1 2,
   opAt 2239 .SUB,
   opAt 2240 .MUL,
   pushAt 2241 2 1664,
   opAt 2242 .MSTORE,
   opAt 2243 .POP,
   opAt 2244 .POP,
   opAt 2245 .POP,
   opAt 2246 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2258 .JUMPDEST,
   opAt 2259 (.Dup ⟨0, by decide⟩),
   opAt 2260 .ISZERO,
   pushAt 2261 2 3535,
   opAt 2262 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2263 (.Dup ⟨1, by decide⟩),
   pushAt 2264 2 512,
   pushAt 2265 2 2080,
   opAt 2266 .MCOPY,
   pushAt 2267 0 0,
   pushAt 2268 2 2784,
   opAt 2269 .MLOAD,
   opAt 2270 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2271 2 512,
   opAt 2272 .MLOAD,
   pushAt 2273 2 1536,
   opAt 2274 .MLOAD,
   opAt 2275 (.Dup ⟨0, by decide⟩),
   opAt 2276 (.Dup ⟨2, by decide⟩),
   opAt 2277 .DIV,
   opAt 2278 (.Swap ⟨1, by decide⟩),
   opAt 2279 .MOD,
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
   pushAt 2335 2 2752,
   opAt 2336 .MLOAD,
   pushAt 2337 2 1280,
   opAt 2338 .ADD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2342 .JUMPDEST,
   opAt 2343 (.Dup ⟨0, by decide⟩),
   opAt 2344 .MLOAD,
   pushAt 2345 0 0,
   opAt 2346 .NOT,
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
   opAt 2366 (.Dup ⟨3, by decide⟩),
   opAt 2367 .MLOAD,
   opAt 2368 .ADD,
   opAt 2369 (.Dup ⟨0, by decide⟩),
   opAt 2370 (.Swap ⟨5, by decide⟩),
   opAt 2371 .GT,
   opAt 2372 .ADD,
   opAt 2373 (.Swap ⟨3, by decide⟩),
   opAt 2374 (.Dup ⟨2, by decide⟩),
   opAt 2375 (.Dup ⟨4, by decide⟩),
   opAt 2376 .ADD,
   opAt 2377 (.Swap ⟨2, by decide⟩),
   opAt 2378 .MSTORE,
   opAt 2379 (.Dup ⟨2, by decide⟩),
   opAt 2380 .ADD,
   pushAt 2498 2 2080,
   opAt 2499 (.Dup ⟨2, by decide⟩),
   opAt 2500 .GT,
   pushAt 2501 2 3183,
   opAt 2502 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2503 .POP,
   opAt 2504 .POP,
   opAt 2505 .POP,
   pushAt 2506 2 2080,
   opAt 2507 .MLOAD,
   opAt 2508 (.Dup ⟨1, by decide⟩),
   opAt 2509 .ADD,
   opAt 2510 (.Dup ⟨0, by decide⟩),
   opAt 2511 (.Swap ⟨1, by decide⟩),
   opAt 2512 .GT,
   opAt 2513 (.Dup ⟨1, by decide⟩),
   opAt 2514 (.Dup ⟨3, by decide⟩),
   opAt 2515 .GT,
   opAt 2516 .GT,
   opAt 2517 (.Swap ⟨1, by decide⟩),
   opAt 2518 (.Swap ⟨0, by decide⟩),
   opAt 2519 .SUB,
   opAt 2520 (.Dup ⟨0, by decide⟩),
   pushAt 2521 2 2080,
   opAt 2522 .MSTORE,
   opAt 2523 (.Dup ⟨1, by decide⟩),
   opAt 2524 .OR,
   pushAt 2525 2 3391,
   opAt 2526 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2534 .JUMPDEST,
   opAt 2535 .ISZERO,
   pushAt 2536 2 3476,
   opAt 2537 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2538 .JUMPDEST,
   pushAt 2539 0 0,
   pushAt 2540 2 2784,
   opAt 2541 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2542 .JUMPDEST,
   opAt 2543 (.Dup ⟨0, by decide⟩),
   opAt 2544 .MLOAD,
   opAt 2545 (.Dup ⟨1, by decide⟩),
   pushAt 2546 2 2112,
   opAt 2547 (.Swap ⟨0, by decide⟩),
   opAt 2548 .SUB,
   opAt 2549 .MLOAD,
   opAt 2550 (.Dup ⟨1, by decide⟩),
   opAt 2551 .ADD,
   opAt 2552 (.Dup ⟨0, by decide⟩),
   opAt 2553 (.Dup ⟨2, by decide⟩),
   opAt 2554 .GT,
   opAt 2555 (.Swap ⟨1, by decide⟩),
   opAt 2556 .POP,
   opAt 2557 (.Dup ⟨3, by decide⟩),
   opAt 2558 .ADD,
   opAt 2559 (.Dup ⟨0, by decide⟩),
   opAt 2560 (.Dup ⟨4, by decide⟩),
   opAt 2561 .GT,
   opAt 2562 (.Swap ⟨3, by decide⟩),
   opAt 2563 .POP,
   opAt 2564 (.Dup ⟨2, by decide⟩),
   opAt 2565 .MSTORE,
   opAt 2566 (.Swap ⟨0, by decide⟩),
   opAt 2567 (.Swap ⟨1, by decide⟩),
   opAt 2568 .OR,
   opAt 2569 (.Swap ⟨0, by decide⟩),
   pushAt 2570 1 31,
   opAt 2571 .NOT,
   opAt 2572 .ADD,
   pushAt 2573 2 2111,
   opAt 2574 (.Dup ⟨1, by decide⟩),
   opAt 2575 .GT,
   pushAt 2576 2 3403,
   opAt 2577 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .POP,
   pushAt 2579 2 2080,
   opAt 2580 .MLOAD,
   opAt 2581 (.Dup ⟨1, by decide⟩),
   opAt 2582 .ADD,
   opAt 2583 (.Dup ⟨0, by decide⟩),
   pushAt 2584 2 2080,
   opAt 2585 .MSTORE,
   opAt 2586 .LT,
   opAt 2587 .ISZERO,
   pushAt 2588 2 3397,
   opAt 2589 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2590 .JUMPDEST,
   pushAt 2591 2 2080,
   opAt 2592 .MLOAD,
   opAt 2593 (.Dup ⟨0, by decide⟩),
   opAt 2594 .ISZERO,
   pushAt 2595 2 3378,
   opAt 2596 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2590 .JUMPDEST,
   pushAt 2591 2 2080,
   opAt 2592 .MLOAD,
   opAt 2593 (.Dup ⟨0, by decide⟩),
   opAt 2594 .ISZERO,
   pushAt 2595 2 3378,
   opAt 2596 .JUMPI,
   opAt 2597 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2598 .JUMPDEST,
   pushAt 2599 0 0,
   pushAt 2600 2 2784,
   opAt 2601 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2602 .JUMPDEST,
   opAt 2603 (.Dup ⟨0, by decide⟩),
   opAt 2604 .MLOAD,
   pushAt 2605 2 2112,
   opAt 2606 (.Dup ⟨2, by decide⟩),
   opAt 2607 .SUB,
   opAt 2608 .MLOAD,
   opAt 2609 (.Dup ⟨1, by decide⟩),
   opAt 2610 (.Dup ⟨1, by decide⟩),
   opAt 2611 .GT,
   opAt 2612 (.Swap ⟨1, by decide⟩),
   opAt 2613 .SUB,
   opAt 2614 (.Dup ⟨3, by decide⟩),
   opAt 2615 (.Dup ⟨1, by decide⟩),
   opAt 2616 .LT,
   opAt 2617 (.Swap ⟨0, by decide⟩),
   opAt 2618 (.Dup ⟨4, by decide⟩),
   opAt 2619 (.Swap ⟨0, by decide⟩),
   opAt 2620 .SUB,
   opAt 2621 (.Dup ⟨3, by decide⟩),
   opAt 2622 .MSTORE,
   opAt 2623 .OR,
   opAt 2624 (.Swap ⟨1, by decide⟩),
   opAt 2625 .POP,
   pushAt 2626 1 31,
   opAt 2627 .NOT,
   opAt 2628 .ADD,
   pushAt 2629 2 2111,
   opAt 2630 (.Dup ⟨1, by decide⟩),
   opAt 2631 .GT,
   pushAt 2632 2 3482,
   opAt 2633 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2634 .POP,
   pushAt 2635 2 2080,
   opAt 2636 .MLOAD,
   opAt 2637 .SUB,
   pushAt 2638 2 2080,
   opAt 2639 .MSTORE,
   pushAt 2640 2 3464,
   opAt 2641 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2527 .JUMPDEST,
   opAt 2528 .NOT,
   opAt 2529 .ADD,
   pushAt 2530 2 3059,
   pushAt 2531 2 512,
   pushAt 2532 2 4337,
   opAt 2533 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2642 .JUMPDEST,
   opAt 2643 .POP,
   pushAt 2644 2 2688,
   opAt 2645 .MLOAD,
   pushAt 2646 2 1280,
   pushAt 2647 2 1024,
   opAt 2648 .MCOPY,
   pushAt 2649 2 2682,
   opAt 2650 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2840 = true :=
  Artifact.isValidJumpDest_index 2098 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2884 = true :=
  Artifact.isValidJumpDest_index 2125 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2901 = true :=
  Artifact.isValidJumpDest_index 2133 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2908 = true :=
  Artifact.isValidJumpDest_index 2137 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2935 = true :=
  Artifact.isValidJumpDest_index 2159 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3059 = true :=
  Artifact.isValidJumpDest_index 2258 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3183 = true :=
  Artifact.isValidJumpDest_index 2342 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3397 = true :=
  Artifact.isValidJumpDest_index 2538 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3403 = true :=
  Artifact.isValidJumpDest_index 2542 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3464 = true :=
  Artifact.isValidJumpDest_index 2590 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3482 = true :=
  Artifact.isValidJumpDest_index 2602 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3391 = true :=
  Artifact.isValidJumpDest_index 2534 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3476 = true :=
  Artifact.isValidJumpDest_index 2598 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3378 = true :=
  Artifact.isValidJumpDest_index 2527 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3535 = true :=
  Artifact.isValidJumpDest_index 2642 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
