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
   pushAt 2116 2 4321,
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
  [opAt 2152 .JUMPDEST,
   opAt 2153 .POP,
   opAt 2154 .POP,
   pushAt 2155 0 0,
   opAt 2156 .MLOAD,
   opAt 2157 (.Dup ⟨0, by decide⟩),
   pushAt 2158 0 0,
   opAt 2159 .SUB,
   opAt 2160 (.Dup ⟨1, by decide⟩),
   opAt 2161 .AND,
   opAt 2162 (.Dup ⟨0, by decide⟩),
   pushAt 2163 2 1536,
   opAt 2164 .MSTORE,
   opAt 2165 (.Dup ⟨0, by decide⟩),
   opAt 2166 (.Dup ⟨2, by decide⟩),
   opAt 2167 .DIV,
   opAt 2168 (.Dup ⟨0, by decide⟩),
   pushAt 2169 2 1568,
   opAt 2170 .MSTORE,
   opAt 2171 (.Dup ⟨1, by decide⟩),
   pushAt 2172 0 0,
   opAt 2173 .SUB,
   opAt 2174 (.Dup ⟨2, by decide⟩),
   opAt 2175 (.Swap ⟨0, by decide⟩),
   opAt 2176 .DIV,
   pushAt 2177 1 1,
   opAt 2178 .ADD,
   pushAt 2179 2 1600,
   opAt 2180 .MSTORE,
   opAt 2181 (.Dup ⟨0, by decide⟩),
   pushAt 2182 0 0,
   opAt 2183 .SUB,
   opAt 2184 (.Dup ⟨1, by decide⟩),
   opAt 2185 (.Swap ⟨0, by decide⟩),
   opAt 2186 .MOD,
   pushAt 2187 2 1632,
   opAt 2188 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2189 (.Dup ⟨0, by decide⟩),
   pushAt 2190 1 3,
   opAt 2191 .MUL,
   pushAt 2192 1 2,
   opAt 2193 .XOR,
   opAt 2194 (.Dup ⟨0, by decide⟩),
   opAt 2195 (.Dup ⟨2, by decide⟩),
   opAt 2196 .MUL,
   pushAt 2197 1 2,
   opAt 2198 .SUB,
   opAt 2199 .MUL,
   opAt 2200 (.Dup ⟨0, by decide⟩),
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
   opAt 2211 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2212 (.Dup ⟨0, by decide⟩),
   opAt 2213 (.Dup ⟨2, by decide⟩),
   opAt 2214 .MUL,
   pushAt 2215 1 2,
   opAt 2216 .SUB,
   opAt 2217 .MUL,
   opAt 2218 (.Dup ⟨0, by decide⟩),
   opAt 2219 (.Dup ⟨2, by decide⟩),
   opAt 2220 .MUL,
   pushAt 2221 1 2,
   opAt 2222 .SUB,
   opAt 2223 .MUL,
   opAt 2224 (.Dup ⟨0, by decide⟩),
   opAt 2225 (.Dup ⟨2, by decide⟩),
   opAt 2226 .MUL,
   pushAt 2227 1 2,
   opAt 2228 .SUB,
   opAt 2229 .MUL,
   pushAt 2230 2 1664,
   opAt 2231 .MSTORE,
   opAt 2232 .POP,
   opAt 2233 .POP,
   opAt 2234 .POP,
   opAt 2235 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2247 .JUMPDEST,
   opAt 2248 (.Dup ⟨0, by decide⟩),
   opAt 2249 .ISZERO,
   pushAt 2250 2 3519,
   opAt 2251 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2252 (.Dup ⟨1, by decide⟩),
   pushAt 2253 2 512,
   pushAt 2254 2 2080,
   opAt 2255 .MCOPY,
   pushAt 2256 0 0,
   pushAt 2257 2 2784,
   opAt 2258 .MLOAD,
   opAt 2259 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2260 2 512,
   opAt 2261 .MLOAD,
   pushAt 2262 2 1536,
   opAt 2263 .MLOAD,
   opAt 2264 (.Dup ⟨0, by decide⟩),
   opAt 2265 (.Dup ⟨2, by decide⟩),
   opAt 2266 .DIV,
   opAt 2267 (.Swap ⟨1, by decide⟩),
   opAt 2268 .MOD,
   pushAt 2269 2 1600,
   opAt 2270 .MLOAD,
   opAt 2271 .MUL,
   pushAt 2272 2 544,
   opAt 2273 .MLOAD,
   pushAt 2274 2 1536,
   opAt 2275 .MLOAD,
   opAt 2276 (.Swap ⟨0, by decide⟩),
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
   pushAt 2322 2 2784,
   opAt 2323 .MLOAD,
   pushAt 2324 0 0,
   opAt 2325 .NOT,
   opAt 2326 (.Swap ⟨0, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2330 .JUMPDEST,
   pushAt 2331 2 832,
   opAt 2332 (.Dup ⟨1, by decide⟩),
   opAt 2333 .SUB,
   opAt 2334 .MLOAD,
   opAt 2335 (.Dup ⟨2, by decide⟩),
   opAt 2336 (.Dup ⟨6, by decide⟩),
   opAt 2337 (.Dup ⟨2, by decide⟩),
   opAt 2338 .MUL,
   opAt 2339 (.Swap ⟨1, by decide⟩),
   opAt 2340 (.Dup ⟨7, by decide⟩),
   opAt 2341 .MULMOD,
   opAt 2342 (.Dup ⟨1, by decide⟩),
   opAt 2343 (.Dup ⟨1, by decide⟩),
   opAt 2344 .LT,
   opAt 2345 .SUB,
   opAt 2346 (.Dup ⟨5, by decide⟩),
   opAt 2347 (.Dup ⟨2, by decide⟩),
   opAt 2348 .ADD,
   opAt 2349 (.Dup ⟨0, by decide⟩),
   opAt 2350 (.Swap ⟨6, by decide⟩),
   opAt 2351 .GT,
   opAt 2352 .SUB,
   opAt 2353 .SUB,
   opAt 2354 (.Dup ⟨4, by decide⟩),
   opAt 2355 (.Dup ⟨2, by decide⟩),
   opAt 2356 .MLOAD,
   opAt 2357 .ADD,
   opAt 2358 (.Dup ⟨0, by decide⟩),
   opAt 2359 (.Swap ⟨5, by decide⟩),
   opAt 2360 .GT,
   opAt 2361 .ADD,
   opAt 2362 (.Swap ⟨3, by decide⟩),
   opAt 2363 (.Dup ⟨1, by decide⟩),
   opAt 2364 .MSTORE,
   opAt 2365 (.Dup ⟨2, by decide⟩),
   opAt 2366 .ADD,
   pushAt 2478 2 2080,
   opAt 2479 (.Dup ⟨1, by decide⟩),
   opAt 2480 .GT,
   pushAt 2481 2 3167,
   opAt 2482 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2483 .POP,
   opAt 2484 .POP,
   opAt 2485 .POP,
   pushAt 2486 2 2080,
   opAt 2487 .MLOAD,
   opAt 2488 (.Dup ⟨1, by decide⟩),
   opAt 2489 .ADD,
   opAt 2490 (.Dup ⟨0, by decide⟩),
   opAt 2491 (.Swap ⟨1, by decide⟩),
   opAt 2492 .GT,
   opAt 2493 (.Dup ⟨1, by decide⟩),
   opAt 2494 (.Dup ⟨3, by decide⟩),
   opAt 2495 .GT,
   opAt 2496 .GT,
   opAt 2497 (.Swap ⟨1, by decide⟩),
   opAt 2498 (.Swap ⟨0, by decide⟩),
   opAt 2499 .SUB,
   opAt 2500 (.Dup ⟨0, by decide⟩),
   pushAt 2501 2 2080,
   opAt 2502 .MSTORE,
   opAt 2503 (.Dup ⟨1, by decide⟩),
   opAt 2504 .OR,
   pushAt 2505 2 3375,
   opAt 2506 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2514 .JUMPDEST,
   opAt 2515 .ISZERO,
   pushAt 2516 2 3460,
   opAt 2517 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2518 .JUMPDEST,
   pushAt 2519 0 0,
   pushAt 2520 2 2784,
   opAt 2521 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2522 .JUMPDEST,
   opAt 2523 (.Dup ⟨0, by decide⟩),
   opAt 2524 .MLOAD,
   opAt 2525 (.Dup ⟨1, by decide⟩),
   pushAt 2526 2 2112,
   opAt 2527 (.Swap ⟨0, by decide⟩),
   opAt 2528 .SUB,
   opAt 2529 .MLOAD,
   opAt 2530 (.Dup ⟨1, by decide⟩),
   opAt 2531 .ADD,
   opAt 2532 (.Dup ⟨0, by decide⟩),
   opAt 2533 (.Dup ⟨2, by decide⟩),
   opAt 2534 .GT,
   opAt 2535 (.Swap ⟨1, by decide⟩),
   opAt 2536 .POP,
   opAt 2537 (.Dup ⟨3, by decide⟩),
   opAt 2538 .ADD,
   opAt 2539 (.Dup ⟨0, by decide⟩),
   opAt 2540 (.Dup ⟨4, by decide⟩),
   opAt 2541 .GT,
   opAt 2542 (.Swap ⟨3, by decide⟩),
   opAt 2543 .POP,
   opAt 2544 (.Dup ⟨2, by decide⟩),
   opAt 2545 .MSTORE,
   opAt 2546 (.Swap ⟨0, by decide⟩),
   opAt 2547 (.Swap ⟨1, by decide⟩),
   opAt 2548 .OR,
   opAt 2549 (.Swap ⟨0, by decide⟩),
   pushAt 2550 1 31,
   opAt 2551 .NOT,
   opAt 2552 .ADD,
   pushAt 2553 2 2111,
   opAt 2554 (.Dup ⟨1, by decide⟩),
   opAt 2555 .GT,
   pushAt 2556 2 3387,
   opAt 2557 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2558 .POP,
   pushAt 2559 2 2080,
   opAt 2560 .MLOAD,
   opAt 2561 (.Dup ⟨1, by decide⟩),
   opAt 2562 .ADD,
   opAt 2563 (.Dup ⟨0, by decide⟩),
   pushAt 2564 2 2080,
   opAt 2565 .MSTORE,
   opAt 2566 .LT,
   opAt 2567 .ISZERO,
   pushAt 2568 2 3381,
   opAt 2569 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2570 .JUMPDEST,
   pushAt 2571 2 2080,
   opAt 2572 .MLOAD,
   opAt 2573 (.Dup ⟨0, by decide⟩),
   opAt 2574 .ISZERO,
   pushAt 2575 2 3362,
   opAt 2576 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2570 .JUMPDEST,
   pushAt 2571 2 2080,
   opAt 2572 .MLOAD,
   opAt 2573 (.Dup ⟨0, by decide⟩),
   opAt 2574 .ISZERO,
   pushAt 2575 2 3362,
   opAt 2576 .JUMPI,
   opAt 2577 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .JUMPDEST,
   pushAt 2579 0 0,
   pushAt 2580 2 2784,
   opAt 2581 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   opAt 2583 (.Dup ⟨0, by decide⟩),
   opAt 2584 .MLOAD,
   pushAt 2585 2 2112,
   opAt 2586 (.Dup ⟨2, by decide⟩),
   opAt 2587 .SUB,
   opAt 2588 .MLOAD,
   opAt 2589 (.Dup ⟨1, by decide⟩),
   opAt 2590 (.Dup ⟨1, by decide⟩),
   opAt 2591 .GT,
   opAt 2592 (.Swap ⟨1, by decide⟩),
   opAt 2593 .SUB,
   opAt 2594 (.Dup ⟨3, by decide⟩),
   opAt 2595 (.Dup ⟨1, by decide⟩),
   opAt 2596 .LT,
   opAt 2597 (.Swap ⟨0, by decide⟩),
   opAt 2598 (.Dup ⟨4, by decide⟩),
   opAt 2599 (.Swap ⟨0, by decide⟩),
   opAt 2600 .SUB,
   opAt 2601 (.Dup ⟨3, by decide⟩),
   opAt 2602 .MSTORE,
   opAt 2603 .OR,
   opAt 2604 (.Swap ⟨1, by decide⟩),
   opAt 2605 .POP,
   pushAt 2606 1 31,
   opAt 2607 .NOT,
   opAt 2608 .ADD,
   pushAt 2609 2 2111,
   opAt 2610 (.Dup ⟨1, by decide⟩),
   opAt 2611 .GT,
   pushAt 2612 2 3466,
   opAt 2613 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2614 .POP,
   pushAt 2615 2 2080,
   opAt 2616 .MLOAD,
   opAt 2617 .SUB,
   pushAt 2618 2 2080,
   opAt 2619 .MSTORE,
   pushAt 2620 2 3448,
   opAt 2621 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2507 .JUMPDEST,
   opAt 2508 .NOT,
   opAt 2509 .ADD,
   pushAt 2510 2 3048,
   pushAt 2511 2 512,
   pushAt 2512 2 4321,
   opAt 2513 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2622 .JUMPDEST,
   opAt 2623 .POP,
   pushAt 2624 2 2688,
   opAt 2625 .MLOAD,
   pushAt 2626 2 1280,
   pushAt 2627 2 1024,
   opAt 2628 .MCOPY,
   pushAt 2629 2 2675,
   opAt 2630 .JUMP]

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2928 = true :=
  Artifact.isValidJumpDest_index 2152 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3048 = true :=
  Artifact.isValidJumpDest_index 2247 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3167 = true :=
  Artifact.isValidJumpDest_index 2330 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3381 = true :=
  Artifact.isValidJumpDest_index 2518 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3387 = true :=
  Artifact.isValidJumpDest_index 2522 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3448 = true :=
  Artifact.isValidJumpDest_index 2570 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3466 = true :=
  Artifact.isValidJumpDest_index 2582 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3375 = true :=
  Artifact.isValidJumpDest_index 2514 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3460 = true :=
  Artifact.isValidJumpDest_index 2578 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3362 = true :=
  Artifact.isValidJumpDest_index 2507 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3519 = true :=
  Artifact.isValidJumpDest_index 2622 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
