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
  [opAt 2050 .JUMPDEST,
   opAt 2051 (.Dup ⟨0, by decide⟩),
   opAt 2052 (.Dup ⟨3, by decide⟩),
   opAt 2053 .EQ,
   pushAt 2054 0 0,
   opAt 2055 .MLOAD,
   pushAt 2056 1 255,
   opAt 2057 .SHR,
   opAt 2058 .AND,
   opAt 2059 .ISZERO,
   pushAt 2060 2 800,
   opAt 2061 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2062 (.Dup ⟨0, by decide⟩),
   pushAt 2063 1 96,
   pushAt 2064 2 2112,
   opAt 2065 .CALLDATACOPY,
   pushAt 2066 0 0,
   pushAt 2067 2 2080,
   opAt 2068 .MSTORE,
   pushAt 2069 2 2508,
   pushAt 2070 2 4229,
   opAt 2071 .JUMP]

def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2077 1 1,
   pushAt 2078 2 2752,
   opAt 2079 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2101 .POP,
   opAt 2102 .POP,
   pushAt 2103 0 0,
   opAt 2104 .MLOAD,
   opAt 2105 (.Dup ⟨0, by decide⟩),
   pushAt 2106 0 0,
   opAt 2107 .SUB,
   opAt 2108 (.Dup ⟨1, by decide⟩),
   opAt 2109 .AND,
   opAt 2110 (.Dup ⟨0, by decide⟩),
   pushAt 2111 2 1536,
   opAt 2112 .MSTORE,
   opAt 2113 (.Dup ⟨0, by decide⟩),
   opAt 2114 (.Dup ⟨2, by decide⟩),
   opAt 2115 .DIV,
   opAt 2116 (.Dup ⟨0, by decide⟩),
   pushAt 2117 2 1568,
   opAt 2118 .MSTORE,
   opAt 2119 (.Dup ⟨1, by decide⟩),
   opAt 2120 (.Dup ⟨0, by decide⟩),
   pushAt 2121 0 0,
   opAt 2122 .SUB,
   opAt 2123 .DIV,
   pushAt 2124 1 1,
   opAt 2125 .ADD,
   pushAt 2126 2 1600,
   opAt 2127 .MSTORE,
   opAt 2128 (.Dup ⟨0, by decide⟩),
   opAt 2129 (.Dup ⟨0, by decide⟩),
   pushAt 2130 0 0,
   opAt 2131 .SUB,
   opAt 2132 .MOD,
   pushAt 2133 2 1632,
   opAt 2134 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2135 (.Dup ⟨0, by decide⟩),
   pushAt 2136 1 3,
   opAt 2137 .MUL,
   pushAt 2138 1 2,
   opAt 2139 .XOR,
   opAt 2140 (.Dup ⟨0, by decide⟩),
   opAt 2141 (.Dup ⟨2, by decide⟩),
   opAt 2142 .MUL,
   pushAt 2143 1 2,
   opAt 2144 .SUB,
   opAt 2145 .MUL,
   opAt 2146 (.Dup ⟨0, by decide⟩),
   opAt 2147 (.Dup ⟨2, by decide⟩),
   opAt 2148 .MUL,
   pushAt 2149 1 2,
   opAt 2150 .SUB,
   opAt 2151 .MUL,
   opAt 2152 (.Dup ⟨0, by decide⟩),
   opAt 2153 (.Dup ⟨2, by decide⟩),
   opAt 2154 .MUL,
   pushAt 2155 1 2,
   opAt 2156 .SUB,
   opAt 2157 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2158 (.Dup ⟨0, by decide⟩),
   opAt 2159 (.Dup ⟨2, by decide⟩),
   opAt 2160 .MUL,
   pushAt 2161 1 2,
   opAt 2162 .SUB,
   opAt 2163 .MUL,
   opAt 2164 (.Dup ⟨0, by decide⟩),
   opAt 2165 (.Dup ⟨2, by decide⟩),
   opAt 2166 .MUL,
   pushAt 2167 1 2,
   opAt 2168 .SUB,
   opAt 2169 .MUL,
   opAt 2170 (.Dup ⟨0, by decide⟩),
   opAt 2171 (.Dup ⟨2, by decide⟩),
   opAt 2172 .MUL,
   pushAt 2173 1 2,
   opAt 2174 .SUB,
   opAt 2175 .MUL,
   pushAt 2176 2 1664,
   opAt 2177 .MSTORE,
   opAt 2178 .POP,
   opAt 2179 .POP,
   opAt 2180 .POP,
   opAt 2181 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2211 .JUMPDEST,
   opAt 2212 (.Dup ⟨0, by decide⟩),
   opAt 2213 .ISZERO,
   pushAt 2214 2 3274,
   opAt 2215 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2216 (.Dup ⟨1, by decide⟩),
   pushAt 2217 2 2112,
   pushAt 2218 2 2080,
   opAt 2219 .MCOPY,
   pushAt 2220 0 0,
   pushAt 2221 2 2784,
   opAt 2222 .MLOAD,
   opAt 2223 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2224 2 2080,
   opAt 2225 .MLOAD,
   pushAt 2226 2 1536,
   opAt 2227 .MLOAD,
   opAt 2228 (.Dup ⟨1, by decide⟩),
   opAt 2229 .DIV,
   opAt 2230 (.Swap ⟨0, by decide⟩),
   pushAt 2231 2 1600,
   opAt 2232 .MLOAD,
   opAt 2233 .MUL,
   pushAt 2234 2 1536,
   opAt 2235 .MLOAD,
   pushAt 2236 2 2112,
   opAt 2237 .MLOAD,
   opAt 2238 .DIV,
   opAt 2239 .ADD,
   pushAt 2240 2 1568,
   opAt 2241 .MLOAD,
   opAt 2242 (.Dup ⟨0, by decide⟩),
   pushAt 2243 2 1632,
   opAt 2244 .MLOAD,
   opAt 2245 (.Dup ⟨4, by decide⟩),
   opAt 2246 .MULMOD,
   opAt 2247 (.Dup ⟨2, by decide⟩),
   opAt 2248 .ADDMOD,
   opAt 2249 (.Swap ⟨0, by decide⟩),
   opAt 2250 .SUB,
   pushAt 2251 2 1664,
   opAt 2252 .MLOAD,
   opAt 2253 .MUL,
   opAt 2254 (.Dup ⟨0, by decide⟩),
   pushAt 2255 0 0,
   opAt 2256 .MLOAD,
   opAt 2257 .MUL,
   pushAt 2258 2 2112,
   opAt 2259 .MLOAD,
   opAt 2260 .SUB,
   pushAt 2261 1 32,
   opAt 2262 .MLOAD,
   pushAt 2263 1 128,
   opAt 2264 .SHR,
   opAt 2265 (.Dup ⟨2, by decide⟩),
   pushAt 2266 1 128,
   opAt 2267 .SHR,
   opAt 2268 .MUL,
   opAt 2269 .GT,
   opAt 2270 (.Swap ⟨0, by decide⟩),
   opAt 2271 .SUB,
   opAt 2272 (.Swap ⟨0, by decide⟩),
   pushAt 2273 2 1568,
   opAt 2274 .MLOAD,
   opAt 2275 .GT,
   opAt 2276 .ISZERO,
   pushAt 2277 0 0,
   opAt 2278 .SUB,
   opAt 2279 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2530 2 2080,
   opAt 2531 .MLOAD,
   opAt 2532 (.Dup ⟨1, by decide⟩),
   opAt 2533 .ADD,
   opAt 2534 (.Dup ⟨0, by decide⟩),
   opAt 2535 (.Swap ⟨1, by decide⟩),
   opAt 2536 .GT,
   opAt 2537 (.Dup ⟨1, by decide⟩),
   opAt 2538 (.Dup ⟨3, by decide⟩),
   opAt 2539 .GT,
   opAt 2540 .GT,
   opAt 2541 (.Swap ⟨1, by decide⟩),
   opAt 2542 (.Swap ⟨0, by decide⟩),
   opAt 2543 .SUB,
   opAt 2544 (.Dup ⟨0, by decide⟩),
   pushAt 2545 2 2080,
   opAt 2546 .MSTORE,
   pushAt 2547 4 3130,
   opAt 2548 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2555 .JUMPDEST,
   opAt 2556 .ISZERO,
   pushAt 2557 2 3215,
   opAt 2558 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2559 .JUMPDEST,
   pushAt 2560 0 0,
   pushAt 2561 2 2784,
   opAt 2562 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2563 .JUMPDEST,
   opAt 2564 (.Dup ⟨0, by decide⟩),
   opAt 2565 .MLOAD,
   pushAt 2566 3 2112,
   opAt 2567 (.Dup ⟨2, by decide⟩),
   opAt 2568 .SUB,
   opAt 2569 .MLOAD,
   opAt 2570 (.Dup ⟨1, by decide⟩),
   opAt 2571 .ADD,
   opAt 2572 (.Swap ⟨0, by decide⟩),
   opAt 2573 (.Dup ⟨1, by decide⟩),
   opAt 2574 .LT,
   opAt 2575 (.Swap ⟨0, by decide⟩),
   opAt 2576 (.Dup ⟨3, by decide⟩),
   opAt 2577 .ADD,
   opAt 2578 (.Swap ⟨2, by decide⟩),
   opAt 2579 (.Dup ⟨3, by decide⟩),
   opAt 2580 .LT,
   opAt 2581 .OR,
   opAt 2582 (.Swap ⟨1, by decide⟩),
   opAt 2583 (.Dup ⟨1, by decide⟩),
   opAt 2584 .MSTORE,
   pushAt 2585 1 31,
   opAt 2586 .NOT,
   opAt 2587 .ADD,
   pushAt 2588 2 2111,
   opAt 2589 (.Dup ⟨1, by decide⟩),
   opAt 2590 .GT,
   pushAt 2591 2 3142,
   opAt 2592 .JUMPI,
   opAt 2593 .JUMPDEST,
   opAt 2594 .JUMPDEST,
   opAt 2595 .JUMPDEST,
   opAt 2596 .JUMPDEST,
   opAt 2597 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2598 .POP,
   pushAt 2599 2 2080,
   opAt 2600 .MLOAD,
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 .ADD,
   opAt 2603 (.Dup ⟨0, by decide⟩),
   pushAt 2604 2 2080,
   opAt 2605 .MSTORE,
   opAt 2606 .LT,
   opAt 2607 .ISZERO,
   pushAt 2608 2 3136,
   opAt 2609 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2610 .JUMPDEST,
   pushAt 2611 2 2080,
   opAt 2612 .MLOAD,
   opAt 2613 (.Dup ⟨0, by decide⟩),
   opAt 2614 .ISZERO,
   pushAt 2615 2 3120,
   opAt 2616 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2610 .JUMPDEST,
   pushAt 2611 2 2080,
   opAt 2612 .MLOAD,
   opAt 2613 (.Dup ⟨0, by decide⟩),
   opAt 2614 .ISZERO,
   pushAt 2615 2 3120,
   opAt 2616 .JUMPI,
   opAt 2617 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2618 .JUMPDEST,
   pushAt 2619 0 0,
   pushAt 2620 2 2784,
   opAt 2621 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2622 .JUMPDEST,
   opAt 2623 (.Dup ⟨0, by decide⟩),
   opAt 2624 .MLOAD,
   pushAt 2625 2 2112,
   opAt 2626 (.Dup ⟨2, by decide⟩),
   opAt 2627 .SUB,
   opAt 2628 .MLOAD,
   opAt 2629 (.Dup ⟨1, by decide⟩),
   opAt 2630 (.Dup ⟨1, by decide⟩),
   opAt 2631 .GT,
   opAt 2632 (.Swap ⟨1, by decide⟩),
   opAt 2633 .SUB,
   opAt 2634 (.Dup ⟨3, by decide⟩),
   opAt 2635 (.Dup ⟨1, by decide⟩),
   opAt 2636 .LT,
   opAt 2637 (.Swap ⟨0, by decide⟩),
   opAt 2638 (.Dup ⟨4, by decide⟩),
   opAt 2639 (.Swap ⟨0, by decide⟩),
   opAt 2640 .SUB,
   opAt 2641 (.Dup ⟨3, by decide⟩),
   opAt 2642 .MSTORE,
   opAt 2643 .OR,
   opAt 2644 (.Swap ⟨1, by decide⟩),
   opAt 2645 .POP,
   pushAt 2646 1 31,
   opAt 2647 .NOT,
   opAt 2648 .ADD,
   pushAt 2649 2 2111,
   opAt 2650 (.Dup ⟨1, by decide⟩),
   opAt 2651 .GT,
   pushAt 2652 2 3221,
   opAt 2653 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2654 .POP,
   pushAt 2655 2 2080,
   opAt 2656 .MLOAD,
   opAt 2657 .SUB,
   pushAt 2658 2 2080,
   opAt 2659 .MSTORE,
   pushAt 2660 2 3203,
   opAt 2661 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2549 .JUMPDEST,
   opAt 2550 .NOT,
   opAt 2551 .ADD,
   pushAt 2552 4 2691,
   opAt 2553 .JUMPDEST,
   opAt 2554 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2682 (.Dup ⟨0, by decide⟩),
   pushAt 2683 2 2112,
   pushAt 2684 2 512,
   opAt 2685 .MCOPY,
   opAt 2686 (.Dup ⟨0, by decide⟩),
   pushAt 2687 2 1280,
   pushAt 2688 2 1024,
   opAt 2689 .MCOPY,
   pushAt 2690 2 2396,
   opAt 2691 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2474 = true :=
  Artifact.isValidJumpDest_index 2050 (by rfl)


theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2508 = true :=
  Artifact.isValidJumpDest_index 2072 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2523 = true :=
  Artifact.isValidJumpDest_index 2080 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2691 = true :=
  Artifact.isValidJumpDest_index 2211 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3136 = true :=
  Artifact.isValidJumpDest_index 2559 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3142 = true :=
  Artifact.isValidJumpDest_index 2563 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3203 = true :=
  Artifact.isValidJumpDest_index 2610 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3221 = true :=
  Artifact.isValidJumpDest_index 2622 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3130 = true :=
  Artifact.isValidJumpDest_index 2555 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3215 = true :=
  Artifact.isValidJumpDest_index 2618 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3120 = true :=
  Artifact.isValidJumpDest_index 2549 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3274 = true :=
  Artifact.isValidJumpDest_index 2662 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
