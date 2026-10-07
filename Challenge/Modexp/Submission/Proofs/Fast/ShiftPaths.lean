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
   pushAt 2088 2 2574,
   pushAt 2089 2 4308,
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
   pushAt 2200 0 0,
   pushAt 2201 0 0,
   opAt 2202 (.Dup ⟨4, by decide⟩),
   opAt 2203 (.Dup ⟨4, by decide⟩),
   opAt 2204 (.Dup ⟨7, by decide⟩),
   pushAt 2205 2 1536,
   opAt 2206 .MLOAD,
   pushAt 2207 2 1568,
   opAt 2208 .MLOAD,
   pushAt 2209 2 1664,
   opAt 2210 .MLOAD,
   pushAt 2211 2 1632,
   opAt 2212 .MLOAD,
   pushAt 2213 2 1504,
   opAt 2214 .MLOAD,
   pushAt 2215 2 1472,
   opAt 2216 .MLOAD,
   pushAt 2217 2 1440,
   opAt 2218 .MLOAD,
   pushAt 2219 2 1408,
   opAt 2220 .MLOAD,
   pushAt 2221 2 1376,
   opAt 2222 .MLOAD,
   pushAt 2223 2 1344,
   opAt 2224 .MLOAD,
   pushAt 2225 2 1312,
   opAt 2226 .MLOAD,
   opAt 2227 (.Dup ⟨12, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2260 .JUMPDEST,
   opAt 2261 (.Dup ⟨0, by decide⟩),
   opAt 2262 .ISZERO,
   pushAt 2263 2 3346,
   opAt 2264 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2265 (.Dup ⟨15, by decide⟩),
   pushAt 2266 2 2112,
   pushAt 2267 2 2080,
   opAt 2268 .MCOPY,
   pushAt 2269 0 0,
   pushAt 2270 2 2784,
   opAt 2271 .MLOAD,
   opAt 2272 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2273 2 2080,
   opAt 2274 .MLOAD,
   opAt 2275 (.Dup ⟨13, by decide⟩),
   opAt 2276 (.Dup ⟨1, by decide⟩),
   opAt 2277 .DIV,
   opAt 2278 (.Swap ⟨0, by decide⟩),
   pushAt 2279 2 1600,
   opAt 2280 .MLOAD,
   opAt 2281 .MUL,
   opAt 2282 (.Dup ⟨14, by decide⟩),
   pushAt 2283 2 2112,
   opAt 2284 .MLOAD,
   opAt 2285 .DIV,
   opAt 2286 .ADD,
   opAt 2287 (.Dup ⟨13, by decide⟩),
   opAt 2288 (.Dup ⟨0, by decide⟩),
   opAt 2289 (.Dup ⟨13, by decide⟩),
   opAt 2290 (.Dup ⟨4, by decide⟩),
   opAt 2291 .MULMOD,
   opAt 2292 (.Dup ⟨2, by decide⟩),
   opAt 2293 .ADDMOD,
   opAt 2294 (.Swap ⟨0, by decide⟩),
   opAt 2295 .SUB,
   opAt 2296 (.Dup ⟨12, by decide⟩),
   opAt 2297 .MUL,
   opAt 2298 (.Dup ⟨0, by decide⟩),
   pushAt 2299 0 0,
   opAt 2300 .MLOAD,
   opAt 2301 .MUL,
   pushAt 2302 2 2112,
   opAt 2303 .MLOAD,
   opAt 2304 .SUB,
   pushAt 2305 1 32,
   opAt 2306 .MLOAD,
   pushAt 2307 1 128,
   opAt 2308 .SHR,
   opAt 2309 (.Dup ⟨2, by decide⟩),
   pushAt 2310 1 128,
   opAt 2311 .SHR,
   opAt 2312 .MUL,
   opAt 2313 .GT,
   opAt 2314 (.Swap ⟨0, by decide⟩),
   opAt 2315 .SUB,
   opAt 2316 (.Swap ⟨0, by decide⟩),
   opAt 2317 (.Dup ⟨13, by decide⟩),
   opAt 2318 .GT,
   opAt 2319 .ISZERO,
   pushAt 2320 0 0,
   opAt 2321 .SUB,
   opAt 2322 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2546 5 2080,
   opAt 2547 .MLOAD,
   opAt 2548 (.Dup ⟨1, by decide⟩),
   opAt 2549 .ADD,
   opAt 2550 (.Dup ⟨0, by decide⟩),
   opAt 2551 (.Swap ⟨1, by decide⟩),
   opAt 2552 .GT,
   opAt 2553 (.Dup ⟨1, by decide⟩),
   opAt 2554 (.Dup ⟨3, by decide⟩),
   opAt 2555 .GT,
   opAt 2556 .GT,
   opAt 2557 (.Swap ⟨2, by decide⟩),
   opAt 2558 .POP,
   opAt 2559 .SUB,
   opAt 2560 (.Dup ⟨0, by decide⟩),
   pushAt 2561 2 2080,
   opAt 2562 .MSTORE,
   opAt 2563 (.Dup ⟨1, by decide⟩),
   opAt 2564 .OR,
   pushAt 2565 2 3208,
   opAt 2566 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2575 .JUMPDEST,
   opAt 2576 .ISZERO,
   pushAt 2577 2 3287,
   opAt 2578 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .JUMPDEST,
   pushAt 2580 0 0,
   pushAt 2581 2 2784,
   opAt 2582 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2583 .JUMPDEST,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   opAt 2585 .MLOAD,
   pushAt 2586 2 2112,
   opAt 2587 (.Dup ⟨2, by decide⟩),
   opAt 2588 .SUB,
   opAt 2589 .MLOAD,
   opAt 2590 (.Dup ⟨1, by decide⟩),
   opAt 2591 .ADD,
   opAt 2592 (.Swap ⟨0, by decide⟩),
   opAt 2593 (.Dup ⟨1, by decide⟩),
   opAt 2594 .LT,
   opAt 2595 (.Swap ⟨0, by decide⟩),
   opAt 2596 (.Dup ⟨3, by decide⟩),
   opAt 2597 .ADD,
   opAt 2598 (.Swap ⟨2, by decide⟩),
   opAt 2599 (.Dup ⟨3, by decide⟩),
   opAt 2600 .LT,
   opAt 2601 .OR,
   opAt 2602 (.Swap ⟨1, by decide⟩),
   opAt 2603 (.Dup ⟨1, by decide⟩),
   opAt 2604 .MSTORE,
   pushAt 2605 1 31,
   opAt 2606 .NOT,
   opAt 2607 .ADD,
   pushAt 2608 2 2111,
   opAt 2609 (.Dup ⟨1, by decide⟩),
   opAt 2610 .GT,
   pushAt 2611 2 3220,
   opAt 2612 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2613 .POP,
   pushAt 2614 2 2080,
   opAt 2615 .MLOAD,
   opAt 2616 (.Dup ⟨1, by decide⟩),
   opAt 2617 .ADD,
   opAt 2618 (.Dup ⟨0, by decide⟩),
   pushAt 2619 2 2080,
   opAt 2620 .MSTORE,
   opAt 2621 .LT,
   opAt 2622 .ISZERO,
   pushAt 2623 2 3214,
   opAt 2624 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2625 .JUMPDEST,
   pushAt 2626 2 2080,
   opAt 2627 .MLOAD,
   opAt 2628 (.Dup ⟨0, by decide⟩),
   opAt 2629 .ISZERO,
   pushAt 2630 2 3198,
   opAt 2631 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2625 .JUMPDEST,
   pushAt 2626 2 2080,
   opAt 2627 .MLOAD,
   opAt 2628 (.Dup ⟨0, by decide⟩),
   opAt 2629 .ISZERO,
   pushAt 2630 2 3198,
   opAt 2631 .JUMPI,
   opAt 2632 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2633 .JUMPDEST,
   pushAt 2634 0 0,
   pushAt 2635 2 2784,
   opAt 2636 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2637 .JUMPDEST,
   opAt 2638 (.Dup ⟨0, by decide⟩),
   opAt 2639 .MLOAD,
   pushAt 2640 2 2112,
   opAt 2641 (.Dup ⟨2, by decide⟩),
   opAt 2642 .SUB,
   opAt 2643 .MLOAD,
   opAt 2644 (.Dup ⟨1, by decide⟩),
   opAt 2645 (.Dup ⟨1, by decide⟩),
   opAt 2646 .GT,
   opAt 2647 (.Swap ⟨1, by decide⟩),
   opAt 2648 .SUB,
   opAt 2649 (.Dup ⟨3, by decide⟩),
   opAt 2650 (.Dup ⟨1, by decide⟩),
   opAt 2651 .LT,
   opAt 2652 (.Swap ⟨0, by decide⟩),
   opAt 2653 (.Dup ⟨4, by decide⟩),
   opAt 2654 (.Swap ⟨0, by decide⟩),
   opAt 2655 .SUB,
   opAt 2656 (.Dup ⟨3, by decide⟩),
   opAt 2657 .MSTORE,
   opAt 2658 .OR,
   opAt 2659 (.Swap ⟨1, by decide⟩),
   opAt 2660 .POP,
   pushAt 2661 1 31,
   opAt 2662 .NOT,
   opAt 2663 .ADD,
   pushAt 2664 2 2111,
   opAt 2665 (.Dup ⟨1, by decide⟩),
   opAt 2666 .GT,
   pushAt 2667 2 3284,
   opAt 2668 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2669 .POP,
   pushAt 2670 2 2080,
   opAt 2671 .MLOAD,
   opAt 2672 .SUB,
   pushAt 2673 2 2080,
   opAt 2674 .MSTORE,
   pushAt 2675 2 3266,
   opAt 2676 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), jump straight to the loop head (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2567 .JUMPDEST,
   opAt 2568 .NOT,
   opAt 2569 .ADD,
   pushAt 2570 2 2811,
   opAt 2571 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2697 2 2441,
   opAt 2698 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2545 = true :=
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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2574 = true :=
  Artifact.isValidJumpDest_index 2091 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2589 = true :=
  Artifact.isValidJumpDest_index 2099 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2811 = true :=
  Artifact.isValidJumpDest_index 2260 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3214 = true :=
  Artifact.isValidJumpDest_index 2579 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3220 = true :=
  Artifact.isValidJumpDest_index 2583 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3275 = true :=
  Artifact.isValidJumpDest_index 2625 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3293 = true :=
  Artifact.isValidJumpDest_index 2637 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3208 = true :=
  Artifact.isValidJumpDest_index 2575 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3287 = true :=
  Artifact.isValidJumpDest_index 2633 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3198 = true :=
  Artifact.isValidJumpDest_index 2567 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3346 = true :=
  Artifact.isValidJumpDest_index 2677 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5444 = true :=
  Artifact.isValidJumpDest_index 4360 (by rfl)

theorem jumpDest3378 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3378 = true :=
  Artifact.isValidJumpDest_index 2696 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2899 + 133·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2228 (.Dup ⟨0, by decide⟩),
   pushAt 2229 1 4,
   opAt 2230 .EQ,
   pushAt 2231 1 133,
   opAt 2232 .MUL,
   pushAt 2233 2 2899,
   opAt 2234 .ADD,
   pushAt 2235 2 1698,
   opAt 2236 .MSTORE,
   opAt 2237 (.Dup ⟨12, by decide⟩),
   pushAt 2238 1 1,
   opAt 2239 .EQ,
   pushAt 2240 2 2816,
   opAt 2241 .MLOAD,
   opAt 2242 .CALLDATALOAD,
   pushAt 2243 0 0,
   opAt 2244 .BYTE,
   pushAt 2245 1 3,
   opAt 2246 .EQ,
   opAt 2247 .AND,
   opAt 2248 (.Dup ⟨1, by decide⟩),
   pushAt 2249 1 3,
   opAt 2250 .AND,
   opAt 2251 .ISZERO,
   opAt 2252 .AND,
   opAt 2253 (.Dup ⟨0, by decide⟩),
   pushAt 2254 2 1760,
   opAt 2255 .MSTORE,
   opAt 2256 .SHR,
   pushAt 2257 2 1698,
   opAt 2258 .MLOAD,
   opAt 2259 (.Swap ⟨0, by decide⟩)]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3377). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2677 .JUMPDEST,
   opAt 2678 .POP,
   pushAt 2679 2 1760,
   opAt 2680 .MLOAD,
   opAt 2681 .ISZERO,
   pushAt 2682 2 5444,
   opAt 2683 .JUMPI]

/-- The cleanup tail (pcs 5444-5465): seventeen `POP`s drop the riding slots,
restoring the bare outer frame, then jump to the done stub. -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4360 .JUMPDEST,
   opAt 4361 .POP,
   opAt 4362 .POP,
   opAt 4363 .POP,
   opAt 4364 .POP,
   opAt 4365 .POP,
   opAt 4366 .POP,
   opAt 4367 .POP,
   opAt 4368 .POP,
   opAt 4369 .POP,
   opAt 4370 .POP,
   opAt 4371 .POP,
   opAt 4372 .POP,
   opAt 4373 .POP,
   opAt 4374 .POP,
   opAt 4375 .POP,
   opAt 4376 .POP,
   opAt 4377 .POP,
   pushAt 4378 2 3378,
   opAt 4379 .JUMP]

/-- The done stub (pcs 3378-3382): jump to the exponent phase's dispatcher. -/
def blk3378 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2696 .JUMPDEST,
   pushAt 2697 2 2441,
   opAt 2698 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
