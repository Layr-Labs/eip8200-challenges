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
   pushAt 2050 2 4299,
   opAt 2051 .JUMP]


/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2057 2 2752,
   opAt 2058 .MLOAD,
   pushAt 2059 1 1]

/-- `blk2919`, first part (pc 2658..2671): the four pads, drop the loop words, and
`L = d &&& -d` twice on top of `d`.  The block stops before the `CLZ` at pc 2672, which the
shared stepper cannot run (`ClzStep.gasSteps_clz`). -/
def blk2919a :
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
   opAt 2090 (.Dup ⟨0, by decide⟩)]

/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2092 (.Dup ⟨0, by decide⟩),
   opAt 2093 .NOT,
   pushAt 2094 0 0,
   opAt 2095 .SUB,
   pushAt 2096 2 1600,
   opAt 2097 .MSTORE,
   pushAt 2098 1 255,
   opAt 2099 .SUB,
   pushAt 2100 2 1536,
   opAt 2101 .MSTORE,
   opAt 2102 (.Dup ⟨0, by decide⟩),
   opAt 2103 (.Dup ⟨2, by decide⟩),
   opAt 2104 .DIV,
   opAt 2105 (.Dup ⟨0, by decide⟩),
   pushAt 2106 2 1568,
   opAt 2107 .MSTORE,
   opAt 2108 (.Dup ⟨0, by decide⟩),
   opAt 2109 (.Dup ⟨0, by decide⟩),
   pushAt 2110 0 0,
   opAt 2111 .SUB,
   opAt 2112 .MOD,
   pushAt 2113 2 1632,
   opAt 2114 .MSTORE]

/-- newton-batch head (pc 2705): load the modulus low limb `n0 = mem[mem[0xac0]]`, call the
shared Newton chain on `dodd * n0` with return pc 2741. -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2115 2 2752,
   opAt 2116 .MLOAD,
   opAt 2117 .MLOAD,
   pushAt 2118 2 2741,
   opAt 2119 (.Dup ⟨1, by decide⟩),
   opAt 2120 (.Dup ⟨3, by decide⟩),
   opAt 2121 .MUL,
   pushAt 2122 2 714,
   opAt 2123 .JUMP]

/-- The shared Newton chain (pc 714): `[p, ret]` becomes `[newton8W p]` at `ret`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 506 .JUMPDEST,
   opAt 507 (.Dup ⟨0, by decide⟩),
   pushAt 508 1 3,
   opAt 509 .MUL,
   pushAt 510 1 2,
   opAt 511 .XOR,
   opAt 512 (.Dup ⟨0, by decide⟩),
   opAt 513 (.Dup ⟨2, by decide⟩),
   opAt 514 .MUL,
   pushAt 515 1 2,
   opAt 516 .SUB,
   opAt 517 .MUL,
   opAt 518 (.Dup ⟨0, by decide⟩),
   opAt 519 (.Dup ⟨2, by decide⟩),
   opAt 520 .MUL,
   pushAt 521 1 2,
   opAt 522 .SUB,
   opAt 523 .MUL,
   opAt 524 (.Dup ⟨0, by decide⟩),
   opAt 525 (.Dup ⟨2, by decide⟩),
   opAt 526 .MUL,
   pushAt 527 1 2,
   opAt 528 .SUB,
   opAt 529 .MUL,
   opAt 530 (.Dup ⟨0, by decide⟩),
   opAt 531 (.Dup ⟨2, by decide⟩),
   opAt 532 .MUL,
   pushAt 533 1 2,
   opAt 534 .SUB,
   opAt 535 .MUL,
   opAt 536 (.Dup ⟨0, by decide⟩),
   opAt 537 (.Dup ⟨2, by decide⟩),
   opAt 538 .MUL,
   pushAt 539 1 2,
   opAt 540 .SUB,
   opAt 541 .MUL,
   opAt 542 (.Dup ⟨0, by decide⟩),
   opAt 543 (.Dup ⟨2, by decide⟩),
   opAt 544 .MUL,
   pushAt 545 1 2,
   opAt 546 .SUB,
   opAt 547 .MUL,
   opAt 548 (.Swap ⟨1, by decide⟩),
   opAt 549 (.Swap ⟨0, by decide⟩),
   opAt 550 .POP,
   opAt 551 .JUMP]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2145 .JUMPDEST,
   opAt 2146 (.Dup ⟨1, by decide⟩),
   opAt 2147 (.Dup ⟨1, by decide⟩),
   opAt 2148 .MUL,
   pushAt 2149 2 1664,
   opAt 2150 .MSTORE,
   opAt 2151 (.Dup ⟨2, by decide⟩),
   opAt 2152 .MUL,
   pushAt 2153 0 0,
   opAt 2154 .SUB,
   pushAt 2155 2 2720,
   opAt 2156 .MSTORE,
   opAt 2157 .POP,
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
  [opAt 2221 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2222 (.Dup ⟨15, by decide⟩),
   pushAt 2223 2 2112,
   pushAt 2224 2 2080,
   opAt 2225 .MCOPY,
   pushAt 2226 0 0,
   pushAt 2227 2 2784,
   opAt 2228 .MLOAD,
   opAt 2229 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2230 2 2080,
   opAt 2231 .MLOAD,
   opAt 2232 (.Dup ⟨0, by decide⟩),
   opAt 2233 (.Dup ⟨14, by decide⟩),
   opAt 2234 .SHR,
   opAt 2235 (.Swap ⟨0, by decide⟩),
   pushAt 2236 2 1600,
   opAt 2237 .MLOAD,
   opAt 2238 .SHL,
   pushAt 2239 2 2112,
   opAt 2240 .MLOAD,
   opAt 2241 (.Dup ⟨15, by decide⟩),
   opAt 2242 .SHR,
   opAt 2243 .ADD,
   opAt 2244 (.Dup ⟨13, by decide⟩),
   opAt 2245 (.Dup ⟨0, by decide⟩),
   opAt 2246 (.Dup ⟨13, by decide⟩),
   opAt 2247 (.Dup ⟨4, by decide⟩),
   opAt 2248 .MULMOD,
   opAt 2249 (.Dup ⟨2, by decide⟩),
   opAt 2250 .ADDMOD,
   opAt 2251 (.Swap ⟨0, by decide⟩),
   opAt 2252 .SUB,
   opAt 2253 (.Dup ⟨12, by decide⟩),
   opAt 2254 .MUL,
   opAt 2255 (.Dup ⟨0, by decide⟩),
   pushAt 2256 0 0,
   opAt 2257 .MLOAD,
   opAt 2258 .MUL,
   pushAt 2259 2 2112,
   opAt 2260 .MLOAD,
   opAt 2261 .SUB,
   pushAt 2262 1 32,
   opAt 2263 .MLOAD,
   pushAt 2264 1 128,
   opAt 2265 .SHR,
   opAt 2266 (.Dup ⟨2, by decide⟩),
   pushAt 2267 1 128,
   opAt 2268 .SHR,
   opAt 2269 .MUL,
   opAt 2270 .GT,
   opAt 2271 (.Swap ⟨0, by decide⟩),
   opAt 2272 .SUB,
   pushAt 2273 0 0,
   opAt 2274 .NOT,
   opAt 2275 (.Swap ⟨1, by decide⟩),
   opAt 2276 (.Dup ⟨14, by decide⟩),
   opAt 2277 .GT,
   opAt 2278 .ISZERO,
   pushAt 2279 0 0,
   opAt 2280 .SUB,
   opAt 2281 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2503 2 2080,
   opAt 2504 .MLOAD,
   opAt 2505 (.Dup ⟨1, by decide⟩),
   opAt 2506 .ADD,
   opAt 2507 (.Dup ⟨0, by decide⟩),
   opAt 2508 (.Swap ⟨1, by decide⟩),
   opAt 2509 .GT,
   opAt 2510 (.Dup ⟨1, by decide⟩),
   opAt 2511 (.Dup ⟨3, by decide⟩),
   opAt 2512 .GT,
   opAt 2513 .GT,
   opAt 2514 (.Swap ⟨2, by decide⟩),
   opAt 2515 .POP,
   opAt 2516 .SUB,
   opAt 2517 (.Dup ⟨0, by decide⟩),
   pushAt 2518 2 2080,
   opAt 2519 .MSTORE,
   opAt 2520 (.Dup ⟨1, by decide⟩),
   opAt 2521 .OR,
   pushAt 2522 2 3228,
   opAt 2523 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2532 .JUMPDEST,
   opAt 2533 .ISZERO,
   pushAt 2534 2 3307,
   opAt 2535 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2536 .JUMPDEST,
   pushAt 2537 0 0,
   pushAt 2538 2 2784,
   opAt 2539 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2540 .JUMPDEST,
   opAt 2541 (.Dup ⟨0, by decide⟩),
   opAt 2542 .MLOAD,
   pushAt 2543 2 2112,
   opAt 2544 (.Dup ⟨2, by decide⟩),
   opAt 2545 .SUB,
   opAt 2546 .MLOAD,
   opAt 2547 (.Dup ⟨1, by decide⟩),
   opAt 2548 .ADD,
   opAt 2549 (.Swap ⟨0, by decide⟩),
   opAt 2550 (.Dup ⟨1, by decide⟩),
   opAt 2551 .LT,
   opAt 2552 (.Swap ⟨0, by decide⟩),
   opAt 2553 (.Dup ⟨3, by decide⟩),
   opAt 2554 .ADD,
   opAt 2555 (.Swap ⟨2, by decide⟩),
   opAt 2556 (.Dup ⟨3, by decide⟩),
   opAt 2557 .LT,
   opAt 2558 .OR,
   opAt 2559 (.Swap ⟨1, by decide⟩),
   opAt 2560 (.Dup ⟨1, by decide⟩),
   opAt 2561 .MSTORE,
   pushAt 2562 1 31,
   opAt 2563 .NOT,
   opAt 2564 .ADD,
   pushAt 2565 2 2111,
   opAt 2566 (.Dup ⟨1, by decide⟩),
   opAt 2567 .GT,
   pushAt 2568 2 3240,
   opAt 2569 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2570 .POP,
   pushAt 2571 2 2080,
   opAt 2572 .MLOAD,
   opAt 2573 (.Dup ⟨1, by decide⟩),
   opAt 2574 .ADD,
   opAt 2575 (.Dup ⟨0, by decide⟩),
   pushAt 2576 2 2080,
   opAt 2577 .MSTORE,
   opAt 2578 .LT,
   opAt 2579 .ISZERO,
   pushAt 2580 2 3234,
   opAt 2581 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   pushAt 2583 2 2080,
   opAt 2584 .MLOAD,
   opAt 2585 (.Dup ⟨0, by decide⟩),
   opAt 2586 .ISZERO,
   pushAt 2587 2 3216,
   opAt 2588 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2582 .JUMPDEST,
   pushAt 2583 2 2080,
   opAt 2584 .MLOAD,
   opAt 2585 (.Dup ⟨0, by decide⟩),
   opAt 2586 .ISZERO,
   pushAt 2587 2 3216,
   opAt 2588 .JUMPI,
   opAt 2589 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2590 .JUMPDEST,
   pushAt 2591 0 0,
   pushAt 2592 2 2784,
   opAt 2593 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2594 .JUMPDEST,
   opAt 2595 (.Dup ⟨0, by decide⟩),
   opAt 2596 .MLOAD,
   pushAt 2597 2 2112,
   opAt 2598 (.Dup ⟨2, by decide⟩),
   opAt 2599 .SUB,
   opAt 2600 .MLOAD,
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 (.Dup ⟨1, by decide⟩),
   opAt 2603 .GT,
   opAt 2604 (.Swap ⟨1, by decide⟩),
   opAt 2605 .SUB,
   opAt 2606 (.Dup ⟨3, by decide⟩),
   opAt 2607 (.Dup ⟨1, by decide⟩),
   opAt 2608 .LT,
   opAt 2609 (.Swap ⟨0, by decide⟩),
   opAt 2610 (.Dup ⟨4, by decide⟩),
   opAt 2611 (.Swap ⟨0, by decide⟩),
   opAt 2612 .SUB,
   opAt 2613 (.Dup ⟨3, by decide⟩),
   opAt 2614 .MSTORE,
   opAt 2615 .OR,
   opAt 2616 (.Swap ⟨1, by decide⟩),
   opAt 2617 .POP,
   pushAt 2618 1 31,
   opAt 2619 .NOT,
   opAt 2620 .ADD,
   pushAt 2621 2 2111,
   opAt 2622 (.Dup ⟨1, by decide⟩),
   opAt 2623 .GT,
   pushAt 2624 2 3284,
   opAt 2625 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2626 .POP,
   pushAt 2627 2 2080,
   opAt 2628 .MLOAD,
   opAt 2629 .SUB,
   pushAt 2630 2 2080,
   opAt 2631 .MSTORE,
   pushAt 2632 2 3266,
   opAt 2633 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2524 .JUMPDEST,
   opAt 2525 .NOT,
   opAt 2526 .ADD,
   opAt 2527 (.Dup ⟨0, by decide⟩),
   pushAt 2528 2 2858,
   opAt 2529 .JUMPI]

/-- The loop exit after the last step: jump to `SHIFT_DONE`. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2530 2 3366,
   opAt 2531 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2592 = true :=
  Artifact.isValidJumpDest_index 2033 (by rfl)

/-- `BAIL6`, the target of the full-base miss. -/
theorem jumpDest714 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 714 = true :=
  Artifact.isValidJumpDest_index 506 (by rfl)

theorem jumpDest2694 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2741 = true :=
  Artifact.isValidJumpDest_index 2145 (by rfl)

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
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3234 = true :=
  Artifact.isValidJumpDest_index 2536 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3240 = true :=
  Artifact.isValidJumpDest_index 2540 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3295 = true :=
  Artifact.isValidJumpDest_index 2582 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3313 = true :=
  Artifact.isValidJumpDest_index 2594 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3228 = true :=
  Artifact.isValidJumpDest_index 2532 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3307 = true :=
  Artifact.isValidJumpDest_index 2590 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3216 = true :=
  Artifact.isValidJumpDest_index 2524 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3366 = true :=
  Artifact.isValidJumpDest_index 2634 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5522 = true :=
  Artifact.isValidJumpDest_index 4392 (by rfl)

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
   pushAt 2194 2 2940,
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
  [opAt 2634 .JUMPDEST,
   opAt 2635 .POP,
   pushAt 2636 2 1760,
   opAt 2637 .MLOAD,
   opAt 2638 .ISZERO,
   pushAt 2639 2 5522,
   opAt 2640 .JUMPI]

/-- The cleanup tail (pcs 5444-5465): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4392 .JUMPDEST,
   opAt 4393 .POP,
   opAt 4394 .POP,
   opAt 4395 .POP,
   opAt 4396 .POP,
   opAt 4397 .POP,
   opAt 4398 .POP,
   opAt 4399 .POP,
   opAt 4400 .POP,
   opAt 4401 .POP,
   opAt 4402 .POP,
   opAt 4403 .POP,
   opAt 4404 .POP,
   opAt 4405 .POP,
   opAt 4406 .POP,
   opAt 4407 .POP,
   opAt 4408 .POP,
   pushAt 4409 2 2492,
   opAt 4410 .ADD,
   opAt 4411 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
