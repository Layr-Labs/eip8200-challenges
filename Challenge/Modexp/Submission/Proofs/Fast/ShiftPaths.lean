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
   pushAt 2101 2 2877,
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
   pushAt 2114 2 2894,
   pushAt 2115 2 512,
   pushAt 2116 2 4317,
   opAt 2117 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2118 .JUMPDEST,
   pushAt 2119 1 1,
   pushAt 2120 2 1024,
   opAt 2121 .MSTORE,
   pushAt 2122 2 892,
   pushAt 2123 2 1024,
   pushAt 2124 2 1670,
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
  [opAt 2244 .JUMPDEST,
   opAt 2245 (.Dup ⟨0, by decide⟩),
   opAt 2246 .ISZERO,
   pushAt 2247 2 3516,
   opAt 2248 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2249 (.Dup ⟨1, by decide⟩),
   pushAt 2250 2 512,
   pushAt 2251 2 2080,
   opAt 2252 .MCOPY,
   pushAt 2253 0 0,
   pushAt 2254 2 2784,
   opAt 2255 .MLOAD,
   opAt 2256 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2257 2 512,
   opAt 2258 .MLOAD,
   pushAt 2259 2 1536,
   opAt 2260 .MLOAD,
   opAt 2261 (.Dup ⟨0, by decide⟩),
   opAt 2262 (.Dup ⟨2, by decide⟩),
   opAt 2263 .DIV,
   opAt 2264 (.Swap ⟨1, by decide⟩),
   opAt 2265 .MOD,
   pushAt 2266 2 1600,
   opAt 2267 .MLOAD,
   opAt 2268 .MUL,
   pushAt 2269 2 544,
   opAt 2270 .MLOAD,
   pushAt 2271 2 1536,
   opAt 2272 .MLOAD,
   opAt 2273 (.Swap ⟨0, by decide⟩),
   opAt 2274 .DIV,
   opAt 2275 .ADD,
   pushAt 2276 2 1568,
   opAt 2277 .MLOAD,
   opAt 2278 (.Dup ⟨0, by decide⟩),
   pushAt 2279 2 1632,
   opAt 2280 .MLOAD,
   opAt 2281 (.Dup ⟨4, by decide⟩),
   opAt 2282 .MULMOD,
   opAt 2283 (.Dup ⟨2, by decide⟩),
   opAt 2284 .ADDMOD,
   opAt 2285 (.Swap ⟨0, by decide⟩),
   opAt 2286 .SUB,
   pushAt 2287 2 1664,
   opAt 2288 .MLOAD,
   opAt 2289 .MUL,
   opAt 2290 (.Dup ⟨0, by decide⟩),
   pushAt 2291 0 0,
   opAt 2292 .MLOAD,
   opAt 2293 .MUL,
   pushAt 2294 2 544,
   opAt 2295 .MLOAD,
   opAt 2296 .SUB,
   pushAt 2297 1 32,
   opAt 2298 .MLOAD,
   pushAt 2299 1 128,
   opAt 2300 .SHR,
   opAt 2301 (.Dup ⟨2, by decide⟩),
   pushAt 2302 1 128,
   opAt 2303 .SHR,
   opAt 2304 .MUL,
   opAt 2305 .GT,
   opAt 2306 (.Swap ⟨0, by decide⟩),
   opAt 2307 .SUB,
   opAt 2308 (.Swap ⟨0, by decide⟩),
   pushAt 2309 2 1568,
   opAt 2310 .MLOAD,
   opAt 2311 .GT,
   opAt 2312 .ISZERO,
   pushAt 2313 0 0,
   opAt 2314 .SUB,
   opAt 2315 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2316 0 0,
   pushAt 2317 1 31,
   opAt 2318 .NOT,
   pushAt 2319 2 2784,
   opAt 2320 .MLOAD,
   pushAt 2321 0 0,
   opAt 2322 .NOT,
   opAt 2323 (.Swap ⟨0, by decide⟩)]

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
   pushAt 2478 2 3164,
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
   pushAt 2502 2 3372,
   opAt 2503 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2511 .JUMPDEST,
   opAt 2512 .ISZERO,
   pushAt 2513 2 3457,
   opAt 2514 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2515 .JUMPDEST,
   pushAt 2516 0 0,
   pushAt 2517 2 2784,
   opAt 2518 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2519 .JUMPDEST,
   opAt 2520 (.Dup ⟨0, by decide⟩),
   opAt 2521 .MLOAD,
   opAt 2522 (.Dup ⟨1, by decide⟩),
   pushAt 2523 2 2112,
   opAt 2524 (.Swap ⟨0, by decide⟩),
   opAt 2525 .SUB,
   opAt 2526 .MLOAD,
   opAt 2527 (.Dup ⟨1, by decide⟩),
   opAt 2528 .ADD,
   opAt 2529 (.Dup ⟨0, by decide⟩),
   opAt 2530 (.Dup ⟨2, by decide⟩),
   opAt 2531 .GT,
   opAt 2532 (.Swap ⟨1, by decide⟩),
   opAt 2533 .POP,
   opAt 2534 (.Dup ⟨3, by decide⟩),
   opAt 2535 .ADD,
   opAt 2536 (.Dup ⟨0, by decide⟩),
   opAt 2537 (.Dup ⟨4, by decide⟩),
   opAt 2538 .GT,
   opAt 2539 (.Swap ⟨3, by decide⟩),
   opAt 2540 .POP,
   opAt 2541 (.Dup ⟨2, by decide⟩),
   opAt 2542 .MSTORE,
   opAt 2543 (.Swap ⟨0, by decide⟩),
   opAt 2544 (.Swap ⟨1, by decide⟩),
   opAt 2545 .OR,
   opAt 2546 (.Swap ⟨0, by decide⟩),
   pushAt 2547 1 31,
   opAt 2548 .NOT,
   opAt 2549 .ADD,
   pushAt 2550 2 2111,
   opAt 2551 (.Dup ⟨1, by decide⟩),
   opAt 2552 .GT,
   pushAt 2553 2 3384,
   opAt 2554 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2555 .POP,
   pushAt 2556 2 2080,
   opAt 2557 .MLOAD,
   opAt 2558 (.Dup ⟨1, by decide⟩),
   opAt 2559 .ADD,
   opAt 2560 (.Dup ⟨0, by decide⟩),
   pushAt 2561 2 2080,
   opAt 2562 .MSTORE,
   opAt 2563 .LT,
   opAt 2564 .ISZERO,
   pushAt 2565 2 3378,
   opAt 2566 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2567 .JUMPDEST,
   pushAt 2568 2 2080,
   opAt 2569 .MLOAD,
   opAt 2570 (.Dup ⟨0, by decide⟩),
   opAt 2571 .ISZERO,
   pushAt 2572 2 3359,
   opAt 2573 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2567 .JUMPDEST,
   pushAt 2568 2 2080,
   opAt 2569 .MLOAD,
   opAt 2570 (.Dup ⟨0, by decide⟩),
   opAt 2571 .ISZERO,
   pushAt 2572 2 3359,
   opAt 2573 .JUMPI,
   opAt 2574 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2575 .JUMPDEST,
   pushAt 2576 0 0,
   pushAt 2577 2 2784,
   opAt 2578 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .JUMPDEST,
   opAt 2580 (.Dup ⟨0, by decide⟩),
   opAt 2581 .MLOAD,
   pushAt 2582 2 2112,
   opAt 2583 (.Dup ⟨2, by decide⟩),
   opAt 2584 .SUB,
   opAt 2585 .MLOAD,
   opAt 2586 (.Dup ⟨1, by decide⟩),
   opAt 2587 (.Dup ⟨1, by decide⟩),
   opAt 2588 .GT,
   opAt 2589 (.Swap ⟨1, by decide⟩),
   opAt 2590 .SUB,
   opAt 2591 (.Dup ⟨3, by decide⟩),
   opAt 2592 (.Dup ⟨1, by decide⟩),
   opAt 2593 .LT,
   opAt 2594 (.Swap ⟨0, by decide⟩),
   opAt 2595 (.Dup ⟨4, by decide⟩),
   opAt 2596 (.Swap ⟨0, by decide⟩),
   opAt 2597 .SUB,
   opAt 2598 (.Dup ⟨3, by decide⟩),
   opAt 2599 .MSTORE,
   opAt 2600 .OR,
   opAt 2601 (.Swap ⟨1, by decide⟩),
   opAt 2602 .POP,
   pushAt 2603 1 31,
   opAt 2604 .NOT,
   opAt 2605 .ADD,
   pushAt 2606 2 2111,
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .GT,
   pushAt 2609 2 3463,
   opAt 2610 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2611 .POP,
   pushAt 2612 2 2080,
   opAt 2613 .MLOAD,
   opAt 2614 .SUB,
   pushAt 2615 2 2080,
   opAt 2616 .MSTORE,
   pushAt 2617 2 3445,
   opAt 2618 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2504 .JUMPDEST,
   opAt 2505 .NOT,
   opAt 2506 .ADD,
   pushAt 2507 2 3045,
   pushAt 2508 2 512,
   pushAt 2509 2 4317,
   opAt 2510 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2619 .JUMPDEST,
   opAt 2620 .POP,
   pushAt 2621 2 2688,
   opAt 2622 .MLOAD,
   pushAt 2623 2 1280,
   pushAt 2624 2 1024,
   opAt 2625 .MCOPY,
   pushAt 2626 2 2675,
   opAt 2627 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2833 = true :=
  Artifact.isValidJumpDest_index 2091 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2877 = true :=
  Artifact.isValidJumpDest_index 2118 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2894 = true :=
  Artifact.isValidJumpDest_index 2126 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2901 = true :=
  Artifact.isValidJumpDest_index 2130 (by rfl)

theorem jumpDest4725 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2927 = true :=
  Artifact.isValidJumpDest_index 2151 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3045 = true :=
  Artifact.isValidJumpDest_index 2244 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3164 = true :=
  Artifact.isValidJumpDest_index 2327 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3378 = true :=
  Artifact.isValidJumpDest_index 2515 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3384 = true :=
  Artifact.isValidJumpDest_index 2519 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3445 = true :=
  Artifact.isValidJumpDest_index 2567 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3463 = true :=
  Artifact.isValidJumpDest_index 2579 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3372 = true :=
  Artifact.isValidJumpDest_index 2511 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3457 = true :=
  Artifact.isValidJumpDest_index 2575 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3359 = true :=
  Artifact.isValidJumpDest_index 2504 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3516 = true :=
  Artifact.isValidJumpDest_index 2619 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
