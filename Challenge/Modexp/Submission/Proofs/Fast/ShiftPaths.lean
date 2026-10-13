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
  [opAt 2033 .JUMPDEST,
   opAt 2034 (.Dup ⟨0, by decide⟩),
   opAt 2035 (.Dup ⟨3, by decide⟩),
   opAt 2036 .EQ,
   pushAt 2037 0 0,
   opAt 2038 .MLOAD,
   pushAt 2039 1 255,
   opAt 2040 .SHR,
   opAt 2041 .AND,
   opAt 2042 .ISZERO,
   pushAt 2043 2 790,
   opAt 2044 .JUMPI]

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
  [opAt 2045 (.Dup ⟨0, by decide⟩),
   pushAt 2046 1 96,
   pushAt 2047 2 2112,
   opAt 2048 .CALLDATACOPY,
   pushAt 2049 2 2621,
   pushAt 2050 2 4309,
   opAt 2051 .JUMP]


/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2057 2 2752,
   opAt 2058 .MLOAD,
   pushAt 2059 1 1]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2077 .JUMPDEST,
   opAt 2078 .JUMPDEST,
   opAt 2079 .JUMPDEST,
   opAt 2080 .JUMPDEST,
   opAt 2081 .POP,
   opAt 2082 .POP,
   pushAt 2083 0 0,
   opAt 2084 .MLOAD,
   opAt 2085 (.Dup ⟨0, by decide⟩),
   pushAt 2086 0 0,
   opAt 2087 .SUB,
   opAt 2088 (.Dup ⟨1, by decide⟩),
   opAt 2089 .AND,
   opAt 2090 (.Dup ⟨0, by decide⟩),
   pushAt 2091 2 1536,
   opAt 2092 .MSTORE,
   opAt 2093 (.Dup ⟨0, by decide⟩),
   opAt 2094 (.Dup ⟨2, by decide⟩),
   opAt 2095 .DIV,
   opAt 2096 (.Dup ⟨0, by decide⟩),
   pushAt 2097 2 1568,
   opAt 2098 .MSTORE,
   opAt 2099 (.Dup ⟨1, by decide⟩),
   opAt 2100 (.Dup ⟨0, by decide⟩),
   pushAt 2101 0 0,
   opAt 2102 .SUB,
   opAt 2103 .DIV,
   pushAt 2104 1 1,
   opAt 2105 .ADD,
   pushAt 2106 2 1600,
   opAt 2107 .MSTORE,
   opAt 2108 (.Dup ⟨0, by decide⟩),
   opAt 2109 (.Dup ⟨0, by decide⟩),
   pushAt 2110 0 0,
   opAt 2111 .SUB,
   opAt 2112 .MOD,
   pushAt 2113 2 1632,
   opAt 2114 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2115 (.Dup ⟨0, by decide⟩),
   pushAt 2116 1 3,
   opAt 2117 .MUL,
   pushAt 2118 1 2,
   opAt 2119 .XOR,
   opAt 2120 (.Dup ⟨0, by decide⟩),
   opAt 2121 (.Dup ⟨2, by decide⟩),
   opAt 2122 .MUL,
   pushAt 2123 1 2,
   opAt 2124 .SUB,
   opAt 2125 .MUL,
   opAt 2126 (.Dup ⟨0, by decide⟩),
   opAt 2127 (.Dup ⟨2, by decide⟩),
   opAt 2128 .MUL,
   pushAt 2129 1 2,
   opAt 2130 .SUB,
   opAt 2131 .MUL,
   opAt 2132 (.Dup ⟨0, by decide⟩),
   opAt 2133 (.Dup ⟨2, by decide⟩),
   opAt 2134 .MUL,
   pushAt 2135 1 2,
   opAt 2136 .SUB,
   opAt 2137 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2138 (.Dup ⟨0, by decide⟩),
   opAt 2139 (.Dup ⟨2, by decide⟩),
   opAt 2140 .MUL,
   pushAt 2141 1 2,
   opAt 2142 .SUB,
   opAt 2143 .MUL,
   opAt 2144 (.Dup ⟨0, by decide⟩),
   opAt 2145 (.Dup ⟨2, by decide⟩),
   opAt 2146 .MUL,
   pushAt 2147 1 2,
   opAt 2148 .SUB,
   opAt 2149 .MUL,
   opAt 2150 (.Dup ⟨0, by decide⟩),
   opAt 2151 (.Dup ⟨2, by decide⟩),
   opAt 2152 .MUL,
   pushAt 2153 1 2,
   opAt 2154 .SUB,
   opAt 2155 .MUL,
   pushAt 2156 2 1664,
   opAt 2157 .MSTORE,
   opAt 2158 .POP,
   opAt 2159 .POP,
   opAt 2160 .POP,
   pushAt 2161 0 0,
   pushAt 2162 0 0,
   opAt 2163 (.Dup ⟨4, by decide⟩),
   opAt 2164 (.Dup ⟨4, by decide⟩),
   opAt 2165 (.Dup ⟨7, by decide⟩),
   pushAt 2166 2 1536,
   opAt 2167 .MLOAD,
   pushAt 2168 2 1568,
   opAt 2169 .MLOAD,
   pushAt 2170 2 1664,
   opAt 2171 .MLOAD,
   pushAt 2172 2 1632,
   opAt 2173 .MLOAD,
   pushAt 2174 2 1504,
   opAt 2175 .MLOAD,
   pushAt 2176 2 1472,
   opAt 2177 .MLOAD,
   pushAt 2178 2 1440,
   opAt 2179 .MLOAD,
   pushAt 2180 2 1408,
   opAt 2181 .MLOAD,
   pushAt 2182 2 1376,
   opAt 2183 .MLOAD,
   pushAt 2184 2 1344,
   opAt 2185 .MLOAD,
   pushAt 2186 2 1312,
   opAt 2187 .MLOAD,
   opAt 2188 (.Dup ⟨12, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2221 .JUMPDEST,
   opAt 2222 (.Dup ⟨0, by decide⟩),
   opAt 2223 .ISZERO,
   pushAt 2224 2 3370,
   opAt 2225 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2226 (.Dup ⟨15, by decide⟩),
   pushAt 2227 2 2112,
   pushAt 2228 2 2080,
   opAt 2229 .MCOPY,
   pushAt 2230 0 0,
   pushAt 2231 2 2784,
   opAt 2232 .MLOAD,
   opAt 2233 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2234 2 2080,
   opAt 2235 .MLOAD,
   opAt 2236 (.Dup ⟨13, by decide⟩),
   opAt 2237 (.Dup ⟨1, by decide⟩),
   opAt 2238 .DIV,
   opAt 2239 (.Swap ⟨0, by decide⟩),
   pushAt 2240 2 1600,
   opAt 2241 .MLOAD,
   opAt 2242 .MUL,
   opAt 2243 (.Dup ⟨14, by decide⟩),
   pushAt 2244 2 2112,
   opAt 2245 .MLOAD,
   opAt 2246 .DIV,
   opAt 2247 .ADD,
   opAt 2248 (.Dup ⟨13, by decide⟩),
   opAt 2249 (.Dup ⟨0, by decide⟩),
   opAt 2250 (.Dup ⟨13, by decide⟩),
   opAt 2251 (.Dup ⟨4, by decide⟩),
   opAt 2252 .MULMOD,
   opAt 2253 (.Dup ⟨2, by decide⟩),
   opAt 2254 .ADDMOD,
   opAt 2255 (.Swap ⟨0, by decide⟩),
   opAt 2256 .SUB,
   opAt 2257 (.Dup ⟨12, by decide⟩),
   opAt 2258 .MUL,
   opAt 2259 (.Dup ⟨0, by decide⟩),
   pushAt 2260 0 0,
   opAt 2261 .MLOAD,
   opAt 2262 .MUL,
   pushAt 2263 2 2112,
   opAt 2264 .MLOAD,
   opAt 2265 .SUB,
   pushAt 2266 1 32,
   opAt 2267 .MLOAD,
   pushAt 2268 1 128,
   opAt 2269 .SHR,
   opAt 2270 (.Dup ⟨2, by decide⟩),
   pushAt 2271 1 128,
   opAt 2272 .SHR,
   opAt 2273 .MUL,
   opAt 2274 .GT,
   opAt 2275 (.Swap ⟨0, by decide⟩),
   opAt 2276 .SUB,
   pushAt 2277 0 0,
   opAt 2278 .NOT,
   opAt 2279 (.Swap ⟨1, by decide⟩),
   opAt 2280 (.Dup ⟨14, by decide⟩),
   opAt 2281 .GT,
   opAt 2282 .ISZERO,
   pushAt 2283 0 0,
   opAt 2284 .SUB,
   opAt 2285 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2507 2 2080,
   opAt 2508 .MLOAD,
   opAt 2509 (.Dup ⟨1, by decide⟩),
   opAt 2510 .ADD,
   opAt 2511 (.Dup ⟨0, by decide⟩),
   opAt 2512 (.Swap ⟨1, by decide⟩),
   opAt 2513 .GT,
   opAt 2514 (.Dup ⟨1, by decide⟩),
   opAt 2515 (.Dup ⟨3, by decide⟩),
   opAt 2516 .GT,
   opAt 2517 .GT,
   opAt 2518 (.Swap ⟨2, by decide⟩),
   opAt 2519 .POP,
   opAt 2520 .SUB,
   opAt 2521 (.Dup ⟨0, by decide⟩),
   pushAt 2522 2 2080,
   opAt 2523 .MSTORE,
   opAt 2524 (.Dup ⟨1, by decide⟩),
   opAt 2525 .OR,
   pushAt 2526 2 3232,
   opAt 2527 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2536 .JUMPDEST,
   opAt 2537 .ISZERO,
   pushAt 2538 2 3311,
   opAt 2539 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2540 .JUMPDEST,
   pushAt 2541 0 0,
   pushAt 2542 2 2784,
   opAt 2543 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2544 .JUMPDEST,
   opAt 2545 (.Dup ⟨0, by decide⟩),
   opAt 2546 .MLOAD,
   pushAt 2547 2 2112,
   opAt 2548 (.Dup ⟨2, by decide⟩),
   opAt 2549 .SUB,
   opAt 2550 .MLOAD,
   opAt 2551 (.Dup ⟨1, by decide⟩),
   opAt 2552 .ADD,
   opAt 2553 (.Swap ⟨0, by decide⟩),
   opAt 2554 (.Dup ⟨1, by decide⟩),
   opAt 2555 .LT,
   opAt 2556 (.Swap ⟨0, by decide⟩),
   opAt 2557 (.Dup ⟨3, by decide⟩),
   opAt 2558 .ADD,
   opAt 2559 (.Swap ⟨2, by decide⟩),
   opAt 2560 (.Dup ⟨3, by decide⟩),
   opAt 2561 .LT,
   opAt 2562 .OR,
   opAt 2563 (.Swap ⟨1, by decide⟩),
   opAt 2564 (.Dup ⟨1, by decide⟩),
   opAt 2565 .MSTORE,
   pushAt 2566 1 31,
   opAt 2567 .NOT,
   opAt 2568 .ADD,
   pushAt 2569 2 2111,
   opAt 2570 (.Dup ⟨1, by decide⟩),
   opAt 2571 .GT,
   pushAt 2572 2 3244,
   opAt 2573 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2574 .POP,
   pushAt 2575 2 2080,
   opAt 2576 .MLOAD,
   opAt 2577 (.Dup ⟨1, by decide⟩),
   opAt 2578 .ADD,
   opAt 2579 (.Dup ⟨0, by decide⟩),
   pushAt 2580 2 2080,
   opAt 2581 .MSTORE,
   opAt 2582 .LT,
   opAt 2583 .ISZERO,
   pushAt 2584 2 3238,
   opAt 2585 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2586 .JUMPDEST,
   pushAt 2587 2 2080,
   opAt 2588 .MLOAD,
   opAt 2589 (.Dup ⟨0, by decide⟩),
   opAt 2590 .ISZERO,
   pushAt 2591 2 3222,
   opAt 2592 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2586 .JUMPDEST,
   pushAt 2587 2 2080,
   opAt 2588 .MLOAD,
   opAt 2589 (.Dup ⟨0, by decide⟩),
   opAt 2590 .ISZERO,
   pushAt 2591 2 3222,
   opAt 2592 .JUMPI,
   opAt 2593 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2594 .JUMPDEST,
   pushAt 2595 0 0,
   pushAt 2596 2 2784,
   opAt 2597 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2598 .JUMPDEST,
   opAt 2599 (.Dup ⟨0, by decide⟩),
   opAt 2600 .MLOAD,
   pushAt 2601 2 2112,
   opAt 2602 (.Dup ⟨2, by decide⟩),
   opAt 2603 .SUB,
   opAt 2604 .MLOAD,
   opAt 2605 (.Dup ⟨1, by decide⟩),
   opAt 2606 (.Dup ⟨1, by decide⟩),
   opAt 2607 .GT,
   opAt 2608 (.Swap ⟨1, by decide⟩),
   opAt 2609 .SUB,
   opAt 2610 (.Dup ⟨3, by decide⟩),
   opAt 2611 (.Dup ⟨1, by decide⟩),
   opAt 2612 .LT,
   opAt 2613 (.Swap ⟨0, by decide⟩),
   opAt 2614 (.Dup ⟨4, by decide⟩),
   opAt 2615 (.Swap ⟨0, by decide⟩),
   opAt 2616 .SUB,
   opAt 2617 (.Dup ⟨3, by decide⟩),
   opAt 2618 .MSTORE,
   opAt 2619 .OR,
   opAt 2620 (.Swap ⟨1, by decide⟩),
   opAt 2621 .POP,
   pushAt 2622 1 31,
   opAt 2623 .NOT,
   opAt 2624 .ADD,
   pushAt 2625 2 2111,
   opAt 2626 (.Dup ⟨1, by decide⟩),
   opAt 2627 .GT,
   pushAt 2628 2 3284,
   opAt 2629 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2630 .POP,
   pushAt 2631 2 2080,
   opAt 2632 .MLOAD,
   opAt 2633 .SUB,
   pushAt 2634 2 2080,
   opAt 2635 .MSTORE,
   pushAt 2636 2 3266,
   opAt 2637 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), jump straight to the loop head (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2528 .JUMPDEST,
   opAt 2529 .NOT,
   opAt 2530 .ADD,
   pushAt 2531 2 2858,
   opAt 2532 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2592 = true :=
  Artifact.isValidJumpDest_index 2033 (by rfl)

/-- `BAIL6`, the target of the full-base miss. -/
theorem jumpDestBail6 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 790 = true :=
  Artifact.isValidJumpDest_index 568 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 238 = true :=
  Artifact.isValidJumpDest_index 165 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2621 = true :=
  Artifact.isValidJumpDest_index 2052 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2636 = true :=
  Artifact.isValidJumpDest_index 2060 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2858 = true :=
  Artifact.isValidJumpDest_index 2221 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3238 = true :=
  Artifact.isValidJumpDest_index 2540 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3244 = true :=
  Artifact.isValidJumpDest_index 2544 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3299 = true :=
  Artifact.isValidJumpDest_index 2586 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3317 = true :=
  Artifact.isValidJumpDest_index 2598 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3232 = true :=
  Artifact.isValidJumpDest_index 2536 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3311 = true :=
  Artifact.isValidJumpDest_index 2594 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3222 = true :=
  Artifact.isValidJumpDest_index 2528 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3370 = true :=
  Artifact.isValidJumpDest_index 2638 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5498 = true :=
  Artifact.isValidJumpDest_index 4370 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2520 = true :=
  Artifact.isValidJumpDest_index 1993 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2946 + 116·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2189 (.Dup ⟨0, by decide⟩),
   pushAt 2190 1 4,
   opAt 2191 .EQ,
   pushAt 2192 1 116,
   opAt 2193 .MUL,
   pushAt 2194 2 2946,
   opAt 2195 .ADD,
   pushAt 2196 2 1698,
   opAt 2197 .MSTORE,
   opAt 2198 (.Dup ⟨12, by decide⟩),
   pushAt 2199 1 1,
   opAt 2200 .EQ,
   pushAt 2201 2 2816,
   opAt 2202 .MLOAD,
   opAt 2203 .CALLDATALOAD,
   pushAt 2204 0 0,
   opAt 2205 .BYTE,
   pushAt 2206 1 3,
   opAt 2207 .EQ,
   opAt 2208 .AND,
   opAt 2209 (.Dup ⟨1, by decide⟩),
   pushAt 2210 1 3,
   opAt 2211 .AND,
   opAt 2212 .ISZERO,
   opAt 2213 .AND,
   opAt 2214 (.Dup ⟨0, by decide⟩),
   pushAt 2215 2 1760,
   opAt 2216 .MSTORE,
   opAt 2217 .SHR,
   pushAt 2218 2 1698,
   opAt 2219 .MLOAD,
   opAt 2220 (.Swap ⟨0, by decide⟩)]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3380). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2638 .JUMPDEST,
   opAt 2639 .POP,
   pushAt 2640 2 1760,
   opAt 2641 .MLOAD,
   opAt 2642 .ISZERO,
   pushAt 2643 2 5498,
   opAt 2644 .JUMPI]

/-- The cleanup tail (pcs 5444-5465): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4370 .JUMPDEST,
   opAt 4371 .POP,
   opAt 4372 .POP,
   opAt 4373 .POP,
   opAt 4374 .POP,
   opAt 4375 .POP,
   opAt 4376 .POP,
   opAt 4377 .POP,
   opAt 4378 .POP,
   opAt 4379 .POP,
   opAt 4380 .POP,
   opAt 4381 .POP,
   opAt 4382 .POP,
   opAt 4383 .POP,
   opAt 4384 .POP,
   opAt 4385 .POP,
   opAt 4386 .POP,
   pushAt 4387 2 2492,
   opAt 4388 .ADD,
   opAt 4389 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
