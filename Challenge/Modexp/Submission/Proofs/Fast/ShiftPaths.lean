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
  [opAt 2069 .JUMPDEST,
   opAt 2070 (.Dup ⟨0, by decide⟩),
   opAt 2071 (.Dup ⟨3, by decide⟩),
   opAt 2072 .EQ,
   pushAt 2073 0 0,
   opAt 2074 .MLOAD,
   pushAt 2075 1 255,
   opAt 2076 .SHR,
   opAt 2077 .AND,
   opAt 2078 .ISZERO,
   pushAt 2079 2 790,
   opAt 2080 .JUMPI]

/-- `BAIL6` (pc 1054): the six-word bail trampoline the full-base miss now names.
It lands on `modexpBig` at pc 237 with the outer frame untouched. -/
def bailBlock :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 568 .JUMPDEST,
   pushAt 569 1 238,
   opAt 570 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2081 (.Dup ⟨0, by decide⟩),
   pushAt 2082 1 96,
   pushAt 2083 2 2112,
   opAt 2084 .CALLDATACOPY,
   pushAt 2085 0 0,
   pushAt 2086 2 2080,
   opAt 2087 .MSTORE,
   pushAt 2088 2 2577,
   pushAt 2089 2 4318,
   opAt 2090 .JUMP]


/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2096 1 1,
   pushAt 2097 2 2752,
   opAt 2098 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2120 .POP,
   opAt 2121 .POP,
   pushAt 2122 0 0,
   opAt 2123 .MLOAD,
   opAt 2124 (.Dup ⟨0, by decide⟩),
   pushAt 2125 0 0,
   opAt 2126 .SUB,
   opAt 2127 (.Dup ⟨1, by decide⟩),
   opAt 2128 .AND,
   opAt 2129 (.Dup ⟨0, by decide⟩),
   pushAt 2130 2 1536,
   opAt 2131 .MSTORE,
   opAt 2132 (.Dup ⟨0, by decide⟩),
   opAt 2133 (.Dup ⟨2, by decide⟩),
   opAt 2134 .DIV,
   opAt 2135 (.Dup ⟨0, by decide⟩),
   pushAt 2136 2 1568,
   opAt 2137 .MSTORE,
   opAt 2138 (.Dup ⟨1, by decide⟩),
   opAt 2139 (.Dup ⟨0, by decide⟩),
   pushAt 2140 0 0,
   opAt 2141 .SUB,
   opAt 2142 .DIV,
   pushAt 2143 1 1,
   opAt 2144 .ADD,
   pushAt 2145 2 1600,
   opAt 2146 .MSTORE,
   opAt 2147 (.Dup ⟨0, by decide⟩),
   opAt 2148 (.Dup ⟨0, by decide⟩),
   pushAt 2149 0 0,
   opAt 2150 .SUB,
   opAt 2151 .MOD,
   pushAt 2152 2 1632,
   opAt 2153 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2154 (.Dup ⟨0, by decide⟩),
   pushAt 2155 1 3,
   opAt 2156 .MUL,
   pushAt 2157 1 2,
   opAt 2158 .XOR,
   opAt 2159 (.Dup ⟨0, by decide⟩),
   opAt 2160 (.Dup ⟨2, by decide⟩),
   opAt 2161 .MUL,
   pushAt 2162 1 2,
   opAt 2163 .SUB,
   opAt 2164 .MUL,
   opAt 2165 (.Dup ⟨0, by decide⟩),
   opAt 2166 (.Dup ⟨2, by decide⟩),
   opAt 2167 .MUL,
   pushAt 2168 1 2,
   opAt 2169 .SUB,
   opAt 2170 .MUL,
   opAt 2171 (.Dup ⟨0, by decide⟩),
   opAt 2172 (.Dup ⟨2, by decide⟩),
   opAt 2173 .MUL,
   pushAt 2174 1 2,
   opAt 2175 .SUB,
   opAt 2176 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2177 (.Dup ⟨0, by decide⟩),
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
   opAt 2194 .MUL,
   pushAt 2195 2 1664,
   opAt 2196 .MSTORE,
   opAt 2197 .POP,
   opAt 2198 .POP,
   opAt 2199 .POP,
   opAt 2200 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2230 .JUMPDEST,
   opAt 2231 (.Dup ⟨0, by decide⟩),
   opAt 2232 .ISZERO,
   pushAt 2233 2 3337,
   opAt 2234 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2235 (.Dup ⟨1, by decide⟩),
   pushAt 2236 2 2112,
   pushAt 2237 2 2080,
   opAt 2238 .MCOPY,
   pushAt 2239 0 0,
   pushAt 2240 2 2784,
   opAt 2241 .MLOAD,
   opAt 2242 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2243 2 2080,
   opAt 2244 .MLOAD,
   pushAt 2245 2 1536,
   opAt 2246 .MLOAD,
   opAt 2247 (.Dup ⟨1, by decide⟩),
   opAt 2248 .DIV,
   opAt 2249 (.Swap ⟨0, by decide⟩),
   pushAt 2250 2 1600,
   opAt 2251 .MLOAD,
   opAt 2252 .MUL,
   pushAt 2253 2 1536,
   opAt 2254 .MLOAD,
   pushAt 2255 2 2112,
   opAt 2256 .MLOAD,
   opAt 2257 .DIV,
   opAt 2258 .ADD,
   pushAt 2259 2 1568,
   opAt 2260 .MLOAD,
   opAt 2261 (.Dup ⟨0, by decide⟩),
   pushAt 2262 2 1632,
   opAt 2263 .MLOAD,
   opAt 2264 (.Dup ⟨4, by decide⟩),
   opAt 2265 .MULMOD,
   opAt 2266 (.Dup ⟨2, by decide⟩),
   opAt 2267 .ADDMOD,
   opAt 2268 (.Swap ⟨0, by decide⟩),
   opAt 2269 .SUB,
   pushAt 2270 2 1664,
   opAt 2271 .MLOAD,
   opAt 2272 .MUL,
   opAt 2273 (.Dup ⟨0, by decide⟩),
   pushAt 2274 0 0,
   opAt 2275 .MLOAD,
   opAt 2276 .MUL,
   pushAt 2277 2 2112,
   opAt 2278 .MLOAD,
   opAt 2279 .SUB,
   pushAt 2280 1 32,
   opAt 2281 .MLOAD,
   pushAt 2282 1 128,
   opAt 2283 .SHR,
   opAt 2284 (.Dup ⟨2, by decide⟩),
   pushAt 2285 1 128,
   opAt 2286 .SHR,
   opAt 2287 .MUL,
   opAt 2288 .GT,
   opAt 2289 (.Swap ⟨0, by decide⟩),
   opAt 2290 .SUB,
   opAt 2291 (.Swap ⟨0, by decide⟩),
   pushAt 2292 2 1568,
   opAt 2293 .MLOAD,
   opAt 2294 .GT,
   opAt 2295 .ISZERO,
   pushAt 2296 0 0,
   opAt 2297 .SUB,
   opAt 2298 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2551 2 2080,
   opAt 2552 .MLOAD,
   opAt 2553 (.Dup ⟨1, by decide⟩),
   opAt 2554 .ADD,
   opAt 2555 (.Dup ⟨0, by decide⟩),
   opAt 2556 (.Swap ⟨1, by decide⟩),
   opAt 2557 .GT,
   opAt 2558 (.Dup ⟨1, by decide⟩),
   opAt 2559 (.Dup ⟨3, by decide⟩),
   opAt 2560 .GT,
   opAt 2561 .GT,
   opAt 2562 (.Swap ⟨1, by decide⟩),
   opAt 2563 (.Swap ⟨0, by decide⟩),
   opAt 2564 .SUB,
   opAt 2565 (.Dup ⟨0, by decide⟩),
   pushAt 2566 2 2080,
   opAt 2567 .MSTORE,
   opAt 2568 (.Dup ⟨1, by decide⟩),
   opAt 2569 .OR,
   pushAt 2570 2 3199,
   opAt 2571 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .JUMPDEST,
   opAt 2579 .ISZERO,
   pushAt 2580 2 3278,
   opAt 2581 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   pushAt 2583 0 0,
   pushAt 2584 2 2784,
   opAt 2585 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2586 .JUMPDEST,
   opAt 2587 (.Dup ⟨0, by decide⟩),
   opAt 2588 .MLOAD,
   pushAt 2589 2 2112,
   opAt 2590 (.Dup ⟨2, by decide⟩),
   opAt 2591 .SUB,
   opAt 2592 .MLOAD,
   opAt 2593 (.Dup ⟨1, by decide⟩),
   opAt 2594 .ADD,
   opAt 2595 (.Swap ⟨0, by decide⟩),
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 .LT,
   opAt 2598 (.Swap ⟨0, by decide⟩),
   opAt 2599 (.Dup ⟨3, by decide⟩),
   opAt 2600 .ADD,
   opAt 2601 (.Swap ⟨2, by decide⟩),
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 .LT,
   opAt 2604 .OR,
   opAt 2605 (.Swap ⟨1, by decide⟩),
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 .MSTORE,
   pushAt 2608 1 31,
   opAt 2609 .NOT,
   opAt 2610 .ADD,
   pushAt 2611 2 2111,
   opAt 2612 (.Dup ⟨1, by decide⟩),
   opAt 2613 .GT,
   pushAt 2614 2 3211,
   opAt 2615 .JUMPI,
]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2616 .POP,
   pushAt 2617 2 2080,
   opAt 2618 .MLOAD,
   opAt 2619 (.Dup ⟨1, by decide⟩),
   opAt 2620 .ADD,
   opAt 2621 (.Dup ⟨0, by decide⟩),
   pushAt 2622 2 2080,
   opAt 2623 .MSTORE,
   opAt 2624 .LT,
   opAt 2625 .ISZERO,
   pushAt 2626 2 3205,
   opAt 2627 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2628 .JUMPDEST,
   pushAt 2629 2 2080,
   opAt 2630 .MLOAD,
   opAt 2631 (.Dup ⟨0, by decide⟩),
   opAt 2632 .ISZERO,
   pushAt 2633 2 3189,
   opAt 2634 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2628 .JUMPDEST,
   pushAt 2629 2 2080,
   opAt 2630 .MLOAD,
   opAt 2631 (.Dup ⟨0, by decide⟩),
   opAt 2632 .ISZERO,
   pushAt 2633 2 3189,
   opAt 2634 .JUMPI,
   opAt 2635 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2636 .JUMPDEST,
   pushAt 2637 0 0,
   pushAt 2638 2 2784,
   opAt 2639 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2640 .JUMPDEST,
   opAt 2641 (.Dup ⟨0, by decide⟩),
   opAt 2642 .MLOAD,
   pushAt 2643 2 2112,
   opAt 2644 (.Dup ⟨2, by decide⟩),
   opAt 2645 .SUB,
   opAt 2646 .MLOAD,
   opAt 2647 (.Dup ⟨1, by decide⟩),
   opAt 2648 (.Dup ⟨1, by decide⟩),
   opAt 2649 .GT,
   opAt 2650 (.Swap ⟨1, by decide⟩),
   opAt 2651 .SUB,
   opAt 2652 (.Dup ⟨3, by decide⟩),
   opAt 2653 (.Dup ⟨1, by decide⟩),
   opAt 2654 .LT,
   opAt 2655 (.Swap ⟨0, by decide⟩),
   opAt 2656 (.Dup ⟨4, by decide⟩),
   opAt 2657 (.Swap ⟨0, by decide⟩),
   opAt 2658 .SUB,
   opAt 2659 (.Dup ⟨3, by decide⟩),
   opAt 2660 .MSTORE,
   opAt 2661 .OR,
   opAt 2662 (.Swap ⟨1, by decide⟩),
   opAt 2663 .POP,
   pushAt 2664 1 31,
   opAt 2665 .NOT,
   opAt 2666 .ADD,
   pushAt 2667 2 2111,
   opAt 2668 (.Dup ⟨1, by decide⟩),
   opAt 2669 .GT,
   pushAt 2670 2 3284,
   opAt 2671 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2672 .POP,
   pushAt 2673 2 2080,
   opAt 2674 .MLOAD,
   opAt 2675 .SUB,
   pushAt 2676 2 2080,
   opAt 2677 .MSTORE,
   pushAt 2678 2 3266,
   opAt 2679 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), jump straight to the loop head (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2572 .JUMPDEST,
   opAt 2573 .NOT,
   opAt 2574 .ADD,
   pushAt 2575 4 2760,
   opAt 2576 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2700 (.Dup ⟨0, by decide⟩),
   pushAt 2701 2 2112,
   pushAt 2702 2 512,
   opAt 2703 .MCOPY,
   opAt 2704 (.Dup ⟨0, by decide⟩),
   pushAt 2705 2 1280,
   pushAt 2706 2 1024,
   opAt 2707 .MCOPY,
   pushAt 2708 2 2441,
   opAt 2709 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2543 = true :=
  Artifact.isValidJumpDest_index 2069 (by rfl)

/-- `BAIL6`, the target of the full-base miss. -/
theorem jumpDestBail6 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 790 = true :=
  Artifact.isValidJumpDest_index 568 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 238 = true :=
  Artifact.isValidJumpDest_index 165 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2577 = true :=
  Artifact.isValidJumpDest_index 2091 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2592 = true :=
  Artifact.isValidJumpDest_index 2099 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2760 = true :=
  Artifact.isValidJumpDest_index 2230 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3205 = true :=
  Artifact.isValidJumpDest_index 2582 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3211 = true :=
  Artifact.isValidJumpDest_index 2586 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3266 = true :=
  Artifact.isValidJumpDest_index 2628 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3284 = true :=
  Artifact.isValidJumpDest_index 2640 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3199 = true :=
  Artifact.isValidJumpDest_index 2578 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3278 = true :=
  Artifact.isValidJumpDest_index 2636 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3189 = true :=
  Artifact.isValidJumpDest_index 2572 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3337 = true :=
  Artifact.isValidJumpDest_index 2680 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
