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
  [opAt 2072 .JUMPDEST,
   opAt 2073 (.Dup ⟨0, by decide⟩),
   opAt 2074 (.Dup ⟨3, by decide⟩),
   opAt 2075 .EQ,
   pushAt 2076 0 0,
   opAt 2077 .MLOAD,
   pushAt 2078 1 255,
   opAt 2079 .SHR,
   opAt 2080 .AND,
   opAt 2081 .ISZERO,
   pushAt 2082 2 790,
   opAt 2083 .JUMPI]

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
  [opAt 2084 (.Dup ⟨0, by decide⟩),
   pushAt 2085 1 96,
   pushAt 2086 2 2112,
   opAt 2087 .CALLDATACOPY,
   pushAt 2088 0 0,
   pushAt 2089 2 2080,
   opAt 2090 .MSTORE,
   pushAt 2091 2 2577,
   pushAt 2092 2 4318,
   opAt 2093 .JUMP]


/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2099 1 1,
   pushAt 2100 2 2752,
   opAt 2101 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2123 .POP,
   opAt 2124 .POP,
   pushAt 2125 0 0,
   opAt 2126 .MLOAD,
   opAt 2127 (.Dup ⟨0, by decide⟩),
   pushAt 2128 0 0,
   opAt 2129 .SUB,
   opAt 2130 (.Dup ⟨1, by decide⟩),
   opAt 2131 .AND,
   opAt 2132 (.Dup ⟨0, by decide⟩),
   pushAt 2133 2 1536,
   opAt 2134 .MSTORE,
   opAt 2135 (.Dup ⟨0, by decide⟩),
   opAt 2136 (.Dup ⟨2, by decide⟩),
   opAt 2137 .DIV,
   opAt 2138 (.Dup ⟨0, by decide⟩),
   pushAt 2139 2 1568,
   opAt 2140 .MSTORE,
   opAt 2141 (.Dup ⟨1, by decide⟩),
   opAt 2142 (.Dup ⟨0, by decide⟩),
   pushAt 2143 0 0,
   opAt 2144 .SUB,
   opAt 2145 .DIV,
   pushAt 2146 1 1,
   opAt 2147 .ADD,
   pushAt 2148 2 1600,
   opAt 2149 .MSTORE,
   opAt 2150 (.Dup ⟨0, by decide⟩),
   opAt 2151 (.Dup ⟨0, by decide⟩),
   pushAt 2152 0 0,
   opAt 2153 .SUB,
   opAt 2154 .MOD,
   pushAt 2155 2 1632,
   opAt 2156 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2157 (.Dup ⟨0, by decide⟩),
   pushAt 2158 1 3,
   opAt 2159 .MUL,
   pushAt 2160 1 2,
   opAt 2161 .XOR,
   opAt 2162 (.Dup ⟨0, by decide⟩),
   opAt 2163 (.Dup ⟨2, by decide⟩),
   opAt 2164 .MUL,
   pushAt 2165 1 2,
   opAt 2166 .SUB,
   opAt 2167 .MUL,
   opAt 2168 (.Dup ⟨0, by decide⟩),
   opAt 2169 (.Dup ⟨2, by decide⟩),
   opAt 2170 .MUL,
   pushAt 2171 1 2,
   opAt 2172 .SUB,
   opAt 2173 .MUL,
   opAt 2174 (.Dup ⟨0, by decide⟩),
   opAt 2175 (.Dup ⟨2, by decide⟩),
   opAt 2176 .MUL,
   pushAt 2177 1 2,
   opAt 2178 .SUB,
   opAt 2179 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2180 (.Dup ⟨0, by decide⟩),
   opAt 2181 (.Dup ⟨2, by decide⟩),
   opAt 2182 .MUL,
   pushAt 2183 1 2,
   opAt 2184 .SUB,
   opAt 2185 .MUL,
   opAt 2186 (.Dup ⟨0, by decide⟩),
   opAt 2187 (.Dup ⟨2, by decide⟩),
   opAt 2188 .MUL,
   pushAt 2189 1 2,
   opAt 2190 .SUB,
   opAt 2191 .MUL,
   opAt 2192 (.Dup ⟨0, by decide⟩),
   opAt 2193 (.Dup ⟨2, by decide⟩),
   opAt 2194 .MUL,
   pushAt 2195 1 2,
   opAt 2196 .SUB,
   opAt 2197 .MUL,
   pushAt 2198 2 1664,
   opAt 2199 .MSTORE,
   opAt 2200 .POP,
   opAt 2201 .POP,
   opAt 2202 .POP,
   opAt 2203 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2233 .JUMPDEST,
   opAt 2234 (.Dup ⟨0, by decide⟩),
   opAt 2235 .ISZERO,
   pushAt 2236 2 3337,
   opAt 2237 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2238 (.Dup ⟨1, by decide⟩),
   pushAt 2239 2 2112,
   pushAt 2240 2 2080,
   opAt 2241 .MCOPY,
   pushAt 2242 0 0,
   pushAt 2243 2 2784,
   opAt 2244 .MLOAD,
   opAt 2245 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2246 2 2080,
   opAt 2247 .MLOAD,
   pushAt 2248 2 1536,
   opAt 2249 .MLOAD,
   opAt 2250 (.Dup ⟨1, by decide⟩),
   opAt 2251 .DIV,
   opAt 2252 (.Swap ⟨0, by decide⟩),
   pushAt 2253 2 1600,
   opAt 2254 .MLOAD,
   opAt 2255 .MUL,
   pushAt 2256 2 1536,
   opAt 2257 .MLOAD,
   pushAt 2258 2 2112,
   opAt 2259 .MLOAD,
   opAt 2260 .DIV,
   opAt 2261 .ADD,
   pushAt 2262 2 1568,
   opAt 2263 .MLOAD,
   opAt 2264 (.Dup ⟨0, by decide⟩),
   pushAt 2265 2 1632,
   opAt 2266 .MLOAD,
   opAt 2267 (.Dup ⟨4, by decide⟩),
   opAt 2268 .MULMOD,
   opAt 2269 (.Dup ⟨2, by decide⟩),
   opAt 2270 .ADDMOD,
   opAt 2271 (.Swap ⟨0, by decide⟩),
   opAt 2272 .SUB,
   pushAt 2273 2 1664,
   opAt 2274 .MLOAD,
   opAt 2275 .MUL,
   opAt 2276 (.Dup ⟨0, by decide⟩),
   pushAt 2277 0 0,
   opAt 2278 .MLOAD,
   opAt 2279 .MUL,
   pushAt 2280 2 2112,
   opAt 2281 .MLOAD,
   opAt 2282 .SUB,
   pushAt 2283 1 32,
   opAt 2284 .MLOAD,
   pushAt 2285 1 128,
   opAt 2286 .SHR,
   opAt 2287 (.Dup ⟨2, by decide⟩),
   pushAt 2288 1 128,
   opAt 2289 .SHR,
   opAt 2290 .MUL,
   opAt 2291 .GT,
   opAt 2292 (.Swap ⟨0, by decide⟩),
   opAt 2293 .SUB,
   opAt 2294 (.Swap ⟨0, by decide⟩),
   pushAt 2295 2 1568,
   opAt 2296 .MLOAD,
   opAt 2297 .GT,
   opAt 2298 .ISZERO,
   pushAt 2299 0 0,
   opAt 2300 .SUB,
   opAt 2301 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2554 2 2080,
   opAt 2555 .MLOAD,
   opAt 2556 (.Dup ⟨1, by decide⟩),
   opAt 2557 .ADD,
   opAt 2558 (.Dup ⟨0, by decide⟩),
   opAt 2559 (.Swap ⟨1, by decide⟩),
   opAt 2560 .GT,
   opAt 2561 (.Dup ⟨1, by decide⟩),
   opAt 2562 (.Dup ⟨3, by decide⟩),
   opAt 2563 .GT,
   opAt 2564 .GT,
   opAt 2565 (.Swap ⟨1, by decide⟩),
   opAt 2566 (.Swap ⟨0, by decide⟩),
   opAt 2567 .SUB,
   opAt 2568 (.Dup ⟨0, by decide⟩),
   pushAt 2569 2 2080,
   opAt 2570 .MSTORE,
   opAt 2571 (.Dup ⟨1, by decide⟩),
   opAt 2572 .OR,
   pushAt 2573 2 3199,
   opAt 2574 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2581 .JUMPDEST,
   opAt 2582 .ISZERO,
   pushAt 2583 2 3278,
   opAt 2584 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2585 .JUMPDEST,
   pushAt 2586 0 0,
   pushAt 2587 2 2784,
   opAt 2588 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2589 .JUMPDEST,
   opAt 2590 (.Dup ⟨0, by decide⟩),
   opAt 2591 .MLOAD,
   pushAt 2592 2 2112,
   opAt 2593 (.Dup ⟨2, by decide⟩),
   opAt 2594 .SUB,
   opAt 2595 .MLOAD,
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 .ADD,
   opAt 2598 (.Swap ⟨0, by decide⟩),
   opAt 2599 (.Dup ⟨1, by decide⟩),
   opAt 2600 .LT,
   opAt 2601 (.Swap ⟨0, by decide⟩),
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 .ADD,
   opAt 2604 (.Swap ⟨2, by decide⟩),
   opAt 2605 (.Dup ⟨3, by decide⟩),
   opAt 2606 .LT,
   opAt 2607 .OR,
   opAt 2608 (.Swap ⟨1, by decide⟩),
   opAt 2609 (.Dup ⟨1, by decide⟩),
   opAt 2610 .MSTORE,
   pushAt 2611 1 31,
   opAt 2612 .NOT,
   opAt 2613 .ADD,
   pushAt 2614 2 2111,
   opAt 2615 (.Dup ⟨1, by decide⟩),
   opAt 2616 .GT,
   pushAt 2617 2 3211,
   opAt 2618 .JUMPI,
]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2619 .POP,
   pushAt 2620 2 2080,
   opAt 2621 .MLOAD,
   opAt 2622 (.Dup ⟨1, by decide⟩),
   opAt 2623 .ADD,
   opAt 2624 (.Dup ⟨0, by decide⟩),
   pushAt 2625 2 2080,
   opAt 2626 .MSTORE,
   opAt 2627 .LT,
   opAt 2628 .ISZERO,
   pushAt 2629 2 3205,
   opAt 2630 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2631 .JUMPDEST,
   pushAt 2632 2 2080,
   opAt 2633 .MLOAD,
   opAt 2634 (.Dup ⟨0, by decide⟩),
   opAt 2635 .ISZERO,
   pushAt 2636 2 3189,
   opAt 2637 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2631 .JUMPDEST,
   pushAt 2632 2 2080,
   opAt 2633 .MLOAD,
   opAt 2634 (.Dup ⟨0, by decide⟩),
   opAt 2635 .ISZERO,
   pushAt 2636 2 3189,
   opAt 2637 .JUMPI,
   opAt 2638 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2639 .JUMPDEST,
   pushAt 2640 0 0,
   pushAt 2641 2 2784,
   opAt 2642 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2643 .JUMPDEST,
   opAt 2644 (.Dup ⟨0, by decide⟩),
   opAt 2645 .MLOAD,
   pushAt 2646 2 2112,
   opAt 2647 (.Dup ⟨2, by decide⟩),
   opAt 2648 .SUB,
   opAt 2649 .MLOAD,
   opAt 2650 (.Dup ⟨1, by decide⟩),
   opAt 2651 (.Dup ⟨1, by decide⟩),
   opAt 2652 .GT,
   opAt 2653 (.Swap ⟨1, by decide⟩),
   opAt 2654 .SUB,
   opAt 2655 (.Dup ⟨3, by decide⟩),
   opAt 2656 (.Dup ⟨1, by decide⟩),
   opAt 2657 .LT,
   opAt 2658 (.Swap ⟨0, by decide⟩),
   opAt 2659 (.Dup ⟨4, by decide⟩),
   opAt 2660 (.Swap ⟨0, by decide⟩),
   opAt 2661 .SUB,
   opAt 2662 (.Dup ⟨3, by decide⟩),
   opAt 2663 .MSTORE,
   opAt 2664 .OR,
   opAt 2665 (.Swap ⟨1, by decide⟩),
   opAt 2666 .POP,
   pushAt 2667 1 31,
   opAt 2668 .NOT,
   opAt 2669 .ADD,
   pushAt 2670 2 2111,
   opAt 2671 (.Dup ⟨1, by decide⟩),
   opAt 2672 .GT,
   pushAt 2673 2 3284,
   opAt 2674 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2675 .POP,
   pushAt 2676 2 2080,
   opAt 2677 .MLOAD,
   opAt 2678 .SUB,
   pushAt 2679 2 2080,
   opAt 2680 .MSTORE,
   pushAt 2681 2 3266,
   opAt 2682 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), jump straight to the loop head (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2575 .JUMPDEST,
   opAt 2576 .NOT,
   opAt 2577 .ADD,
   pushAt 2578 4 2760,
   opAt 2579 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2703 (.Dup ⟨0, by decide⟩),
   pushAt 2704 2 2112,
   pushAt 2705 2 512,
   opAt 2706 .MCOPY,
   opAt 2707 (.Dup ⟨0, by decide⟩),
   pushAt 2708 2 1280,
   pushAt 2709 2 1024,
   opAt 2710 .MCOPY,
   pushAt 2711 2 2441,
   opAt 2712 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2543 = true :=
  Artifact.isValidJumpDest_index 2072 (by rfl)

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
  Artifact.isValidJumpDest_index 2094 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2592 = true :=
  Artifact.isValidJumpDest_index 2102 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2760 = true :=
  Artifact.isValidJumpDest_index 2233 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3205 = true :=
  Artifact.isValidJumpDest_index 2585 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3211 = true :=
  Artifact.isValidJumpDest_index 2589 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3266 = true :=
  Artifact.isValidJumpDest_index 2631 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3284 = true :=
  Artifact.isValidJumpDest_index 2643 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3199 = true :=
  Artifact.isValidJumpDest_index 2581 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3278 = true :=
  Artifact.isValidJumpDest_index 2639 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3189 = true :=
  Artifact.isValidJumpDest_index 2575 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3337 = true :=
  Artifact.isValidJumpDest_index 2683 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
