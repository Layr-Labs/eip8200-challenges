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
  [opAt 2070 .JUMPDEST,
   opAt 2071 (.Dup ⟨0, by decide⟩),
   opAt 2072 (.Dup ⟨3, by decide⟩),
   opAt 2073 .EQ,
   pushAt 2074 0 0,
   opAt 2075 .MLOAD,
   pushAt 2076 1 255,
   opAt 2077 .SHR,
   opAt 2078 .AND,
   opAt 2079 .ISZERO,
   pushAt 2080 2 790,
   opAt 2081 .JUMPI]

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
  [opAt 2082 (.Dup ⟨0, by decide⟩),
   pushAt 2083 1 96,
   pushAt 2084 2 2112,
   opAt 2085 .CALLDATACOPY,
   pushAt 2086 0 0,
   pushAt 2087 2 2080,
   opAt 2088 .MSTORE,
   pushAt 2089 2 2577,
   pushAt 2090 2 4318,
   opAt 2091 .JUMP]


/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2097 1 1,
   pushAt 2098 2 2752,
   opAt 2099 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2121 .POP,
   opAt 2122 .POP,
   pushAt 2123 0 0,
   opAt 2124 .MLOAD,
   opAt 2125 (.Dup ⟨0, by decide⟩),
   pushAt 2126 0 0,
   opAt 2127 .SUB,
   opAt 2128 (.Dup ⟨1, by decide⟩),
   opAt 2129 .AND,
   opAt 2130 (.Dup ⟨0, by decide⟩),
   pushAt 2131 2 1536,
   opAt 2132 .MSTORE,
   opAt 2133 (.Dup ⟨0, by decide⟩),
   opAt 2134 (.Dup ⟨2, by decide⟩),
   opAt 2135 .DIV,
   opAt 2136 (.Dup ⟨0, by decide⟩),
   pushAt 2137 2 1568,
   opAt 2138 .MSTORE,
   opAt 2139 (.Dup ⟨1, by decide⟩),
   opAt 2140 (.Dup ⟨0, by decide⟩),
   pushAt 2141 0 0,
   opAt 2142 .SUB,
   opAt 2143 .DIV,
   pushAt 2144 1 1,
   opAt 2145 .ADD,
   pushAt 2146 2 1600,
   opAt 2147 .MSTORE,
   opAt 2148 (.Dup ⟨0, by decide⟩),
   opAt 2149 (.Dup ⟨0, by decide⟩),
   pushAt 2150 0 0,
   opAt 2151 .SUB,
   opAt 2152 .MOD,
   pushAt 2153 2 1632,
   opAt 2154 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2155 (.Dup ⟨0, by decide⟩),
   pushAt 2156 1 3,
   opAt 2157 .MUL,
   pushAt 2158 1 2,
   opAt 2159 .XOR,
   opAt 2160 (.Dup ⟨0, by decide⟩),
   opAt 2161 (.Dup ⟨2, by decide⟩),
   opAt 2162 .MUL,
   pushAt 2163 1 2,
   opAt 2164 .SUB,
   opAt 2165 .MUL,
   opAt 2166 (.Dup ⟨0, by decide⟩),
   opAt 2167 (.Dup ⟨2, by decide⟩),
   opAt 2168 .MUL,
   pushAt 2169 1 2,
   opAt 2170 .SUB,
   opAt 2171 .MUL,
   opAt 2172 (.Dup ⟨0, by decide⟩),
   opAt 2173 (.Dup ⟨2, by decide⟩),
   opAt 2174 .MUL,
   pushAt 2175 1 2,
   opAt 2176 .SUB,
   opAt 2177 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2178 (.Dup ⟨0, by decide⟩),
   opAt 2179 (.Dup ⟨2, by decide⟩),
   opAt 2180 .MUL,
   pushAt 2181 1 2,
   opAt 2182 .SUB,
   opAt 2183 .MUL,
   opAt 2184 (.Dup ⟨0, by decide⟩),
   opAt 2185 (.Dup ⟨2, by decide⟩),
   opAt 2186 .MUL,
   pushAt 2187 1 2,
   opAt 2188 .SUB,
   opAt 2189 .MUL,
   opAt 2190 (.Dup ⟨0, by decide⟩),
   opAt 2191 (.Dup ⟨2, by decide⟩),
   opAt 2192 .MUL,
   pushAt 2193 1 2,
   opAt 2194 .SUB,
   opAt 2195 .MUL,
   pushAt 2196 2 1664,
   opAt 2197 .MSTORE,
   opAt 2198 .POP,
   opAt 2199 .POP,
   opAt 2200 .POP,
   opAt 2201 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2231 .JUMPDEST,
   opAt 2232 (.Dup ⟨0, by decide⟩),
   opAt 2233 .ISZERO,
   pushAt 2234 2 3337,
   opAt 2235 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2236 (.Dup ⟨1, by decide⟩),
   pushAt 2237 2 2112,
   pushAt 2238 2 2080,
   opAt 2239 .MCOPY,
   pushAt 2240 0 0,
   pushAt 2241 2 2784,
   opAt 2242 .MLOAD,
   opAt 2243 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2244 2 2080,
   opAt 2245 .MLOAD,
   pushAt 2246 2 1536,
   opAt 2247 .MLOAD,
   opAt 2248 (.Dup ⟨1, by decide⟩),
   opAt 2249 .DIV,
   opAt 2250 (.Swap ⟨0, by decide⟩),
   pushAt 2251 2 1600,
   opAt 2252 .MLOAD,
   opAt 2253 .MUL,
   pushAt 2254 2 1536,
   opAt 2255 .MLOAD,
   pushAt 2256 2 2112,
   opAt 2257 .MLOAD,
   opAt 2258 .DIV,
   opAt 2259 .ADD,
   pushAt 2260 2 1568,
   opAt 2261 .MLOAD,
   opAt 2262 (.Dup ⟨0, by decide⟩),
   pushAt 2263 2 1632,
   opAt 2264 .MLOAD,
   opAt 2265 (.Dup ⟨4, by decide⟩),
   opAt 2266 .MULMOD,
   opAt 2267 (.Dup ⟨2, by decide⟩),
   opAt 2268 .ADDMOD,
   opAt 2269 (.Swap ⟨0, by decide⟩),
   opAt 2270 .SUB,
   pushAt 2271 2 1664,
   opAt 2272 .MLOAD,
   opAt 2273 .MUL,
   opAt 2274 (.Dup ⟨0, by decide⟩),
   pushAt 2275 0 0,
   opAt 2276 .MLOAD,
   opAt 2277 .MUL,
   pushAt 2278 2 2112,
   opAt 2279 .MLOAD,
   opAt 2280 .SUB,
   pushAt 2281 1 32,
   opAt 2282 .MLOAD,
   pushAt 2283 1 128,
   opAt 2284 .SHR,
   opAt 2285 (.Dup ⟨2, by decide⟩),
   pushAt 2286 1 128,
   opAt 2287 .SHR,
   opAt 2288 .MUL,
   opAt 2289 .GT,
   opAt 2290 (.Swap ⟨0, by decide⟩),
   opAt 2291 .SUB,
   opAt 2292 (.Swap ⟨0, by decide⟩),
   pushAt 2293 2 1568,
   opAt 2294 .MLOAD,
   opAt 2295 .GT,
   opAt 2296 .ISZERO,
   pushAt 2297 0 0,
   opAt 2298 .SUB,
   opAt 2299 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2552 2 2080,
   opAt 2553 .MLOAD,
   opAt 2554 (.Dup ⟨1, by decide⟩),
   opAt 2555 .ADD,
   opAt 2556 (.Dup ⟨0, by decide⟩),
   opAt 2557 (.Swap ⟨1, by decide⟩),
   opAt 2558 .GT,
   opAt 2559 (.Dup ⟨1, by decide⟩),
   opAt 2560 (.Dup ⟨3, by decide⟩),
   opAt 2561 .GT,
   opAt 2562 .GT,
   opAt 2563 (.Swap ⟨1, by decide⟩),
   opAt 2564 (.Swap ⟨0, by decide⟩),
   opAt 2565 .SUB,
   opAt 2566 (.Dup ⟨0, by decide⟩),
   pushAt 2567 2 2080,
   opAt 2568 .MSTORE,
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .OR,
   pushAt 2571 2 3199,
   opAt 2572 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .JUMPDEST,
   opAt 2580 .ISZERO,
   pushAt 2581 2 3278,
   opAt 2582 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .JUMPDEST,
   pushAt 2584 0 0,
   pushAt 2585 2 2784,
   opAt 2586 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2587 .JUMPDEST,
   opAt 2588 (.Dup ⟨0, by decide⟩),
   opAt 2589 .MLOAD,
   pushAt 2590 2 2112,
   opAt 2591 (.Dup ⟨2, by decide⟩),
   opAt 2592 .SUB,
   opAt 2593 .MLOAD,
   opAt 2594 (.Dup ⟨1, by decide⟩),
   opAt 2595 .ADD,
   opAt 2596 (.Swap ⟨0, by decide⟩),
   opAt 2597 (.Dup ⟨1, by decide⟩),
   opAt 2598 .LT,
   opAt 2599 (.Swap ⟨0, by decide⟩),
   opAt 2600 (.Dup ⟨3, by decide⟩),
   opAt 2601 .ADD,
   opAt 2602 (.Swap ⟨2, by decide⟩),
   opAt 2603 (.Dup ⟨3, by decide⟩),
   opAt 2604 .LT,
   opAt 2605 .OR,
   opAt 2606 (.Swap ⟨1, by decide⟩),
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .MSTORE,
   pushAt 2609 1 31,
   opAt 2610 .NOT,
   opAt 2611 .ADD,
   pushAt 2612 2 2111,
   opAt 2613 (.Dup ⟨1, by decide⟩),
   opAt 2614 .GT,
   pushAt 2615 2 3211,
   opAt 2616 .JUMPI,
]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2617 .POP,
   pushAt 2618 2 2080,
   opAt 2619 .MLOAD,
   opAt 2620 (.Dup ⟨1, by decide⟩),
   opAt 2621 .ADD,
   opAt 2622 (.Dup ⟨0, by decide⟩),
   pushAt 2623 2 2080,
   opAt 2624 .MSTORE,
   opAt 2625 .LT,
   opAt 2626 .ISZERO,
   pushAt 2627 2 3205,
   opAt 2628 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2629 .JUMPDEST,
   pushAt 2630 2 2080,
   opAt 2631 .MLOAD,
   opAt 2632 (.Dup ⟨0, by decide⟩),
   opAt 2633 .ISZERO,
   pushAt 2634 2 3189,
   opAt 2635 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2629 .JUMPDEST,
   pushAt 2630 2 2080,
   opAt 2631 .MLOAD,
   opAt 2632 (.Dup ⟨0, by decide⟩),
   opAt 2633 .ISZERO,
   pushAt 2634 2 3189,
   opAt 2635 .JUMPI,
   opAt 2636 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2637 .JUMPDEST,
   pushAt 2638 0 0,
   pushAt 2639 2 2784,
   opAt 2640 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2641 .JUMPDEST,
   opAt 2642 (.Dup ⟨0, by decide⟩),
   opAt 2643 .MLOAD,
   pushAt 2644 2 2112,
   opAt 2645 (.Dup ⟨2, by decide⟩),
   opAt 2646 .SUB,
   opAt 2647 .MLOAD,
   opAt 2648 (.Dup ⟨1, by decide⟩),
   opAt 2649 (.Dup ⟨1, by decide⟩),
   opAt 2650 .GT,
   opAt 2651 (.Swap ⟨1, by decide⟩),
   opAt 2652 .SUB,
   opAt 2653 (.Dup ⟨3, by decide⟩),
   opAt 2654 (.Dup ⟨1, by decide⟩),
   opAt 2655 .LT,
   opAt 2656 (.Swap ⟨0, by decide⟩),
   opAt 2657 (.Dup ⟨4, by decide⟩),
   opAt 2658 (.Swap ⟨0, by decide⟩),
   opAt 2659 .SUB,
   opAt 2660 (.Dup ⟨3, by decide⟩),
   opAt 2661 .MSTORE,
   opAt 2662 .OR,
   opAt 2663 (.Swap ⟨1, by decide⟩),
   opAt 2664 .POP,
   pushAt 2665 1 31,
   opAt 2666 .NOT,
   opAt 2667 .ADD,
   pushAt 2668 2 2111,
   opAt 2669 (.Dup ⟨1, by decide⟩),
   opAt 2670 .GT,
   pushAt 2671 2 3284,
   opAt 2672 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2673 .POP,
   pushAt 2674 2 2080,
   opAt 2675 .MLOAD,
   opAt 2676 .SUB,
   pushAt 2677 2 2080,
   opAt 2678 .MSTORE,
   pushAt 2679 2 3266,
   opAt 2680 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), jump straight to the loop head (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2573 .JUMPDEST,
   opAt 2574 .NOT,
   opAt 2575 .ADD,
   pushAt 2576 4 2760,
   opAt 2577 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2701 (.Dup ⟨0, by decide⟩),
   pushAt 2702 2 2112,
   pushAt 2703 2 512,
   opAt 2704 .MCOPY,
   opAt 2705 (.Dup ⟨0, by decide⟩),
   pushAt 2706 2 1280,
   pushAt 2707 2 1024,
   opAt 2708 .MCOPY,
   pushAt 2709 2 2441,
   opAt 2710 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2543 = true :=
  Artifact.isValidJumpDest_index 2070 (by rfl)

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
  Artifact.isValidJumpDest_index 2092 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2592 = true :=
  Artifact.isValidJumpDest_index 2100 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2760 = true :=
  Artifact.isValidJumpDest_index 2231 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3205 = true :=
  Artifact.isValidJumpDest_index 2583 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3211 = true :=
  Artifact.isValidJumpDest_index 2587 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3266 = true :=
  Artifact.isValidJumpDest_index 2629 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3284 = true :=
  Artifact.isValidJumpDest_index 2641 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3199 = true :=
  Artifact.isValidJumpDest_index 2579 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3278 = true :=
  Artifact.isValidJumpDest_index 2637 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3189 = true :=
  Artifact.isValidJumpDest_index 2573 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3337 = true :=
  Artifact.isValidJumpDest_index 2681 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
