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
  [opAt 2031 .JUMPDEST,
   opAt 2032 (.Dup ⟨0, by decide⟩),
   opAt 2033 (.Dup ⟨3, by decide⟩),
   opAt 2034 .EQ,
   pushAt 2035 0 0,
   opAt 2036 .MLOAD,
   pushAt 2037 1 255,
   opAt 2038 .SHR,
   opAt 2039 .AND,
   opAt 2040 .ISZERO,
   pushAt 2041 2 800,
   opAt 2042 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2043 (.Dup ⟨0, by decide⟩),
   pushAt 2044 1 96,
   pushAt 2045 2 2112,
   opAt 2046 .CALLDATACOPY,
   pushAt 2047 0 0,
   pushAt 2048 2 2080,
   opAt 2049 .MSTORE,
   pushAt 2050 2 2508,
   pushAt 2051 2 4229,
   opAt 2052 .JUMP]

def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2058 1 1,
   pushAt 2059 2 2752,
   opAt 2060 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2082 .POP,
   opAt 2083 .POP,
   pushAt 2084 0 0,
   opAt 2085 .MLOAD,
   opAt 2086 (.Dup ⟨0, by decide⟩),
   pushAt 2087 0 0,
   opAt 2088 .SUB,
   opAt 2089 (.Dup ⟨1, by decide⟩),
   opAt 2090 .AND,
   opAt 2091 (.Dup ⟨0, by decide⟩),
   pushAt 2092 2 1536,
   opAt 2093 .MSTORE,
   opAt 2094 (.Dup ⟨0, by decide⟩),
   opAt 2095 (.Dup ⟨2, by decide⟩),
   opAt 2096 .DIV,
   opAt 2097 (.Dup ⟨0, by decide⟩),
   pushAt 2098 2 1568,
   opAt 2099 .MSTORE,
   opAt 2100 (.Dup ⟨1, by decide⟩),
   opAt 2101 (.Dup ⟨0, by decide⟩),
   pushAt 2102 0 0,
   opAt 2103 .SUB,
   opAt 2104 .DIV,
   pushAt 2105 1 1,
   opAt 2106 .ADD,
   pushAt 2107 2 1600,
   opAt 2108 .MSTORE,
   opAt 2109 (.Dup ⟨0, by decide⟩),
   opAt 2110 (.Dup ⟨0, by decide⟩),
   pushAt 2111 0 0,
   opAt 2112 .SUB,
   opAt 2113 .MOD,
   pushAt 2114 2 1632,
   opAt 2115 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2116 (.Dup ⟨0, by decide⟩),
   pushAt 2117 1 3,
   opAt 2118 .MUL,
   pushAt 2119 1 2,
   opAt 2120 .XOR,
   opAt 2121 (.Dup ⟨0, by decide⟩),
   opAt 2122 (.Dup ⟨2, by decide⟩),
   opAt 2123 .MUL,
   pushAt 2124 1 2,
   opAt 2125 .SUB,
   opAt 2126 .MUL,
   opAt 2127 (.Dup ⟨0, by decide⟩),
   opAt 2128 (.Dup ⟨2, by decide⟩),
   opAt 2129 .MUL,
   pushAt 2130 1 2,
   opAt 2131 .SUB,
   opAt 2132 .MUL,
   opAt 2133 (.Dup ⟨0, by decide⟩),
   opAt 2134 (.Dup ⟨2, by decide⟩),
   opAt 2135 .MUL,
   pushAt 2136 1 2,
   opAt 2137 .SUB,
   opAt 2138 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2139 (.Dup ⟨0, by decide⟩),
   opAt 2140 (.Dup ⟨2, by decide⟩),
   opAt 2141 .MUL,
   pushAt 2142 1 2,
   opAt 2143 .SUB,
   opAt 2144 .MUL,
   opAt 2145 (.Dup ⟨0, by decide⟩),
   opAt 2146 (.Dup ⟨2, by decide⟩),
   opAt 2147 .MUL,
   pushAt 2148 1 2,
   opAt 2149 .SUB,
   opAt 2150 .MUL,
   opAt 2151 (.Dup ⟨0, by decide⟩),
   opAt 2152 (.Dup ⟨2, by decide⟩),
   opAt 2153 .MUL,
   pushAt 2154 1 2,
   opAt 2155 .SUB,
   opAt 2156 .MUL,
   pushAt 2157 2 1664,
   opAt 2158 .MSTORE,
   opAt 2159 .POP,
   opAt 2160 .POP,
   opAt 2161 .POP,
   opAt 2162 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2192 .JUMPDEST,
   opAt 2193 (.Dup ⟨0, by decide⟩),
   opAt 2194 .ISZERO,
   pushAt 2195 2 3274,
   opAt 2196 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2197 (.Dup ⟨1, by decide⟩),
   pushAt 2198 2 2112,
   pushAt 2199 2 2080,
   opAt 2200 .MCOPY,
   pushAt 2201 0 0,
   pushAt 2202 2 2784,
   opAt 2203 .MLOAD,
   opAt 2204 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2205 2 2080,
   opAt 2206 .MLOAD,
   pushAt 2207 2 1536,
   opAt 2208 .MLOAD,
   opAt 2209 (.Dup ⟨1, by decide⟩),
   opAt 2210 .DIV,
   opAt 2211 (.Swap ⟨0, by decide⟩),
   pushAt 2212 2 1600,
   opAt 2213 .MLOAD,
   opAt 2214 .MUL,
   pushAt 2215 2 1536,
   opAt 2216 .MLOAD,
   pushAt 2217 2 2112,
   opAt 2218 .MLOAD,
   opAt 2219 .DIV,
   opAt 2220 .ADD,
   pushAt 2221 2 1568,
   opAt 2222 .MLOAD,
   opAt 2223 (.Dup ⟨0, by decide⟩),
   pushAt 2224 2 1632,
   opAt 2225 .MLOAD,
   opAt 2226 (.Dup ⟨4, by decide⟩),
   opAt 2227 .MULMOD,
   opAt 2228 (.Dup ⟨2, by decide⟩),
   opAt 2229 .ADDMOD,
   opAt 2230 (.Swap ⟨0, by decide⟩),
   opAt 2231 .SUB,
   pushAt 2232 2 1664,
   opAt 2233 .MLOAD,
   opAt 2234 .MUL,
   opAt 2235 (.Dup ⟨0, by decide⟩),
   pushAt 2236 0 0,
   opAt 2237 .MLOAD,
   opAt 2238 .MUL,
   pushAt 2239 2 2112,
   opAt 2240 .MLOAD,
   opAt 2241 .SUB,
   pushAt 2242 1 32,
   opAt 2243 .MLOAD,
   pushAt 2244 1 128,
   opAt 2245 .SHR,
   opAt 2246 (.Dup ⟨2, by decide⟩),
   pushAt 2247 1 128,
   opAt 2248 .SHR,
   opAt 2249 .MUL,
   opAt 2250 .GT,
   opAt 2251 (.Swap ⟨0, by decide⟩),
   opAt 2252 .SUB,
   opAt 2253 (.Swap ⟨0, by decide⟩),
   pushAt 2254 2 1568,
   opAt 2255 .MLOAD,
   opAt 2256 .GT,
   opAt 2257 .ISZERO,
   pushAt 2258 0 0,
   opAt 2259 .SUB,
   opAt 2260 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2511 2 2080,
   opAt 2512 .MLOAD,
   opAt 2513 (.Dup ⟨1, by decide⟩),
   opAt 2514 .ADD,
   opAt 2515 (.Dup ⟨0, by decide⟩),
   opAt 2516 (.Swap ⟨1, by decide⟩),
   opAt 2517 .GT,
   opAt 2518 (.Dup ⟨1, by decide⟩),
   opAt 2519 (.Dup ⟨3, by decide⟩),
   opAt 2520 .GT,
   opAt 2521 .GT,
   opAt 2522 (.Swap ⟨1, by decide⟩),
   opAt 2523 (.Swap ⟨0, by decide⟩),
   opAt 2524 .SUB,
   opAt 2525 (.Dup ⟨0, by decide⟩),
   pushAt 2526 2 2080,
   opAt 2527 .MSTORE,
   pushAt 2528 4 3130,
   opAt 2529 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2536 .JUMPDEST,
   opAt 2537 .ISZERO,
   pushAt 2538 2 3215,
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
   pushAt 2547 3 2112,
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
   pushAt 2572 2 3142,
   opAt 2573 .JUMPI,
   opAt 2574 .JUMPDEST,
   opAt 2575 .JUMPDEST,
   opAt 2576 .JUMPDEST,
   opAt 2577 .JUMPDEST,
   opAt 2578 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .POP,
   pushAt 2580 2 2080,
   opAt 2581 .MLOAD,
   opAt 2582 (.Dup ⟨1, by decide⟩),
   opAt 2583 .ADD,
   opAt 2584 (.Dup ⟨0, by decide⟩),
   pushAt 2585 2 2080,
   opAt 2586 .MSTORE,
   opAt 2587 .LT,
   opAt 2588 .ISZERO,
   pushAt 2589 2 3136,
   opAt 2590 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2591 .JUMPDEST,
   pushAt 2592 2 2080,
   opAt 2593 .MLOAD,
   opAt 2594 (.Dup ⟨0, by decide⟩),
   opAt 2595 .ISZERO,
   pushAt 2596 2 3120,
   opAt 2597 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2591 .JUMPDEST,
   pushAt 2592 2 2080,
   opAt 2593 .MLOAD,
   opAt 2594 (.Dup ⟨0, by decide⟩),
   opAt 2595 .ISZERO,
   pushAt 2596 2 3120,
   opAt 2597 .JUMPI,
   opAt 2598 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2599 .JUMPDEST,
   pushAt 2600 0 0,
   pushAt 2601 2 2784,
   opAt 2602 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2603 .JUMPDEST,
   opAt 2604 (.Dup ⟨0, by decide⟩),
   opAt 2605 .MLOAD,
   pushAt 2606 2 2112,
   opAt 2607 (.Dup ⟨2, by decide⟩),
   opAt 2608 .SUB,
   opAt 2609 .MLOAD,
   opAt 2610 (.Dup ⟨1, by decide⟩),
   opAt 2611 (.Dup ⟨1, by decide⟩),
   opAt 2612 .GT,
   opAt 2613 (.Swap ⟨1, by decide⟩),
   opAt 2614 .SUB,
   opAt 2615 (.Dup ⟨3, by decide⟩),
   opAt 2616 (.Dup ⟨1, by decide⟩),
   opAt 2617 .LT,
   opAt 2618 (.Swap ⟨0, by decide⟩),
   opAt 2619 (.Dup ⟨4, by decide⟩),
   opAt 2620 (.Swap ⟨0, by decide⟩),
   opAt 2621 .SUB,
   opAt 2622 (.Dup ⟨3, by decide⟩),
   opAt 2623 .MSTORE,
   opAt 2624 .OR,
   opAt 2625 (.Swap ⟨1, by decide⟩),
   opAt 2626 .POP,
   pushAt 2627 1 31,
   opAt 2628 .NOT,
   opAt 2629 .ADD,
   pushAt 2630 2 2111,
   opAt 2631 (.Dup ⟨1, by decide⟩),
   opAt 2632 .GT,
   pushAt 2633 2 3221,
   opAt 2634 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2635 .POP,
   pushAt 2636 2 2080,
   opAt 2637 .MLOAD,
   opAt 2638 .SUB,
   pushAt 2639 2 2080,
   opAt 2640 .MSTORE,
   pushAt 2641 2 3203,
   opAt 2642 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2530 .JUMPDEST,
   opAt 2531 .NOT,
   opAt 2532 .ADD,
   pushAt 2533 4 2691,
   opAt 2534 .JUMPDEST,
   opAt 2535 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2663 (.Dup ⟨0, by decide⟩),
   pushAt 2664 2 2112,
   pushAt 2665 2 512,
   opAt 2666 .MCOPY,
   opAt 2667 (.Dup ⟨0, by decide⟩),
   pushAt 2668 2 1280,
   pushAt 2669 2 1024,
   opAt 2670 .MCOPY,
   pushAt 2671 2 2396,
   opAt 2672 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2474 = true :=
  Artifact.isValidJumpDest_index 2031 (by rfl)


theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2508 = true :=
  Artifact.isValidJumpDest_index 2053 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2523 = true :=
  Artifact.isValidJumpDest_index 2061 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2691 = true :=
  Artifact.isValidJumpDest_index 2192 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3136 = true :=
  Artifact.isValidJumpDest_index 2540 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3142 = true :=
  Artifact.isValidJumpDest_index 2544 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3203 = true :=
  Artifact.isValidJumpDest_index 2591 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3221 = true :=
  Artifact.isValidJumpDest_index 2603 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3130 = true :=
  Artifact.isValidJumpDest_index 2536 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3215 = true :=
  Artifact.isValidJumpDest_index 2599 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3120 = true :=
  Artifact.isValidJumpDest_index 2530 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3274 = true :=
  Artifact.isValidJumpDest_index 2643 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
