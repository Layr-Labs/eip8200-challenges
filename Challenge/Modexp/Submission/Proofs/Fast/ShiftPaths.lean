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
  [opAt 2018 .JUMPDEST,
   opAt 2019 (.Dup ⟨0, by decide⟩),
   opAt 2020 (.Dup ⟨3, by decide⟩),
   opAt 2021 .EQ,
   pushAt 2022 0 0,
   opAt 2023 .MLOAD,
   pushAt 2024 1 255,
   opAt 2025 .SHR,
   opAt 2026 .AND,
   opAt 2027 .ISZERO,
   pushAt 2028 2 800,
   opAt 2029 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2030 (.Dup ⟨0, by decide⟩),
   pushAt 2031 1 96,
   pushAt 2032 2 2112,
   opAt 2033 .CALLDATACOPY,
   pushAt 2034 0 0,
   pushAt 2035 2 2080,
   opAt 2036 .MSTORE,
   pushAt 2037 2 2508,
   pushAt 2038 2 4240,
   opAt 2039 .JUMP]

def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2045 1 1,
   pushAt 2046 2 2752,
   opAt 2047 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2069 .POP,
   opAt 2070 .POP,
   pushAt 2071 0 0,
   opAt 2072 .MLOAD,
   opAt 2073 (.Dup ⟨0, by decide⟩),
   pushAt 2074 0 0,
   opAt 2075 .SUB,
   opAt 2076 (.Dup ⟨1, by decide⟩),
   opAt 2077 .AND,
   opAt 2078 (.Dup ⟨0, by decide⟩),
   pushAt 2079 2 1536,
   opAt 2080 .MSTORE,
   opAt 2081 (.Dup ⟨0, by decide⟩),
   opAt 2082 (.Dup ⟨2, by decide⟩),
   opAt 2083 .DIV,
   opAt 2084 (.Dup ⟨0, by decide⟩),
   pushAt 2085 2 1568,
   opAt 2086 .MSTORE,
   opAt 2087 (.Dup ⟨1, by decide⟩),
   opAt 2088 (.Dup ⟨0, by decide⟩),
   pushAt 2089 0 0,
   opAt 2090 .SUB,
   opAt 2091 .DIV,
   pushAt 2092 1 1,
   opAt 2093 .ADD,
   pushAt 2094 2 1600,
   opAt 2095 .MSTORE,
   opAt 2096 (.Dup ⟨0, by decide⟩),
   opAt 2097 (.Dup ⟨0, by decide⟩),
   pushAt 2098 0 0,
   opAt 2099 .SUB,
   opAt 2100 .MOD,
   pushAt 2101 2 1632,
   opAt 2102 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2103 (.Dup ⟨0, by decide⟩),
   pushAt 2104 1 3,
   opAt 2105 .MUL,
   pushAt 2106 1 2,
   opAt 2107 .XOR,
   opAt 2108 (.Dup ⟨0, by decide⟩),
   opAt 2109 (.Dup ⟨2, by decide⟩),
   opAt 2110 .MUL,
   pushAt 2111 1 2,
   opAt 2112 .SUB,
   opAt 2113 .MUL,
   opAt 2114 (.Dup ⟨0, by decide⟩),
   opAt 2115 (.Dup ⟨2, by decide⟩),
   opAt 2116 .MUL,
   pushAt 2117 1 2,
   opAt 2118 .SUB,
   opAt 2119 .MUL,
   opAt 2120 (.Dup ⟨0, by decide⟩),
   opAt 2121 (.Dup ⟨2, by decide⟩),
   opAt 2122 .MUL,
   pushAt 2123 1 2,
   opAt 2124 .SUB,
   opAt 2125 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2126 (.Dup ⟨0, by decide⟩),
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
   opAt 2137 .MUL,
   opAt 2138 (.Dup ⟨0, by decide⟩),
   opAt 2139 (.Dup ⟨2, by decide⟩),
   opAt 2140 .MUL,
   pushAt 2141 1 2,
   opAt 2142 .SUB,
   opAt 2143 .MUL,
   pushAt 2144 2 1664,
   opAt 2145 .MSTORE,
   opAt 2146 .POP,
   opAt 2147 .POP,
   opAt 2148 .POP,
   opAt 2149 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2179 .JUMPDEST,
   opAt 2180 (.Dup ⟨0, by decide⟩),
   opAt 2181 .ISZERO,
   pushAt 2182 2 3274,
   opAt 2183 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2184 (.Dup ⟨1, by decide⟩),
   pushAt 2185 2 2112,
   pushAt 2186 2 2080,
   opAt 2187 .MCOPY,
   pushAt 2188 0 0,
   pushAt 2189 2 2784,
   opAt 2190 .MLOAD,
   opAt 2191 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2192 2 2080,
   opAt 2193 .MLOAD,
   pushAt 2194 2 1536,
   opAt 2195 .MLOAD,
   opAt 2196 (.Dup ⟨1, by decide⟩),
   opAt 2197 .DIV,
   opAt 2198 (.Swap ⟨0, by decide⟩),
   pushAt 2199 2 1600,
   opAt 2200 .MLOAD,
   opAt 2201 .MUL,
   pushAt 2202 2 1536,
   opAt 2203 .MLOAD,
   pushAt 2204 2 2112,
   opAt 2205 .MLOAD,
   opAt 2206 .DIV,
   opAt 2207 .ADD,
   pushAt 2208 2 1568,
   opAt 2209 .MLOAD,
   opAt 2210 (.Dup ⟨0, by decide⟩),
   pushAt 2211 2 1632,
   opAt 2212 .MLOAD,
   opAt 2213 (.Dup ⟨4, by decide⟩),
   opAt 2214 .MULMOD,
   opAt 2215 (.Dup ⟨2, by decide⟩),
   opAt 2216 .ADDMOD,
   opAt 2217 (.Swap ⟨0, by decide⟩),
   opAt 2218 .SUB,
   pushAt 2219 2 1664,
   opAt 2220 .MLOAD,
   opAt 2221 .MUL,
   opAt 2222 (.Dup ⟨0, by decide⟩),
   pushAt 2223 0 0,
   opAt 2224 .MLOAD,
   opAt 2225 .MUL,
   pushAt 2226 2 2112,
   opAt 2227 .MLOAD,
   opAt 2228 .SUB,
   pushAt 2229 1 32,
   opAt 2230 .MLOAD,
   pushAt 2231 1 128,
   opAt 2232 .SHR,
   opAt 2233 (.Dup ⟨2, by decide⟩),
   pushAt 2234 1 128,
   opAt 2235 .SHR,
   opAt 2236 .MUL,
   opAt 2237 .GT,
   opAt 2238 (.Swap ⟨0, by decide⟩),
   opAt 2239 .SUB,
   opAt 2240 (.Swap ⟨0, by decide⟩),
   pushAt 2241 2 1568,
   opAt 2242 .MLOAD,
   opAt 2243 .GT,
   opAt 2244 .ISZERO,
   pushAt 2245 0 0,
   opAt 2246 .SUB,
   opAt 2247 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2498 2 2080,
   opAt 2499 .MLOAD,
   opAt 2500 (.Dup ⟨1, by decide⟩),
   opAt 2501 .ADD,
   opAt 2502 (.Dup ⟨0, by decide⟩),
   opAt 2503 (.Swap ⟨1, by decide⟩),
   opAt 2504 .GT,
   opAt 2505 (.Dup ⟨1, by decide⟩),
   opAt 2506 (.Dup ⟨3, by decide⟩),
   opAt 2507 .GT,
   opAt 2508 .GT,
   opAt 2509 (.Swap ⟨1, by decide⟩),
   opAt 2510 (.Swap ⟨0, by decide⟩),
   opAt 2511 .SUB,
   opAt 2512 (.Dup ⟨0, by decide⟩),
   pushAt 2513 2 2080,
   opAt 2514 .MSTORE,
   pushAt 2515 4 3130,
   opAt 2516 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2523 .JUMPDEST,
   opAt 2524 .ISZERO,
   pushAt 2525 2 3215,
   opAt 2526 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2527 .JUMPDEST,
   pushAt 2528 0 0,
   pushAt 2529 2 2784,
   opAt 2530 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2531 .JUMPDEST,
   opAt 2532 (.Dup ⟨0, by decide⟩),
   opAt 2533 .MLOAD,
   pushAt 2534 3 2112,
   opAt 2535 (.Dup ⟨2, by decide⟩),
   opAt 2536 .SUB,
   opAt 2537 .MLOAD,
   opAt 2538 (.Dup ⟨1, by decide⟩),
   opAt 2539 .ADD,
   opAt 2540 (.Swap ⟨0, by decide⟩),
   opAt 2541 (.Dup ⟨1, by decide⟩),
   opAt 2542 .LT,
   opAt 2543 (.Swap ⟨0, by decide⟩),
   opAt 2544 (.Dup ⟨3, by decide⟩),
   opAt 2545 .ADD,
   opAt 2546 (.Swap ⟨2, by decide⟩),
   opAt 2547 (.Dup ⟨3, by decide⟩),
   opAt 2548 .LT,
   opAt 2549 .OR,
   opAt 2550 (.Swap ⟨1, by decide⟩),
   opAt 2551 (.Dup ⟨1, by decide⟩),
   opAt 2552 .MSTORE,
   pushAt 2553 1 31,
   opAt 2554 .NOT,
   opAt 2555 .ADD,
   pushAt 2556 2 2111,
   opAt 2557 (.Dup ⟨1, by decide⟩),
   opAt 2558 .GT,
   pushAt 2559 2 3142,
   opAt 2560 .JUMPI,
   opAt 2561 .JUMPDEST,
   opAt 2562 .JUMPDEST,
   opAt 2563 .JUMPDEST,
   opAt 2564 .JUMPDEST,
   opAt 2565 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2566 .POP,
   pushAt 2567 2 2080,
   opAt 2568 .MLOAD,
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .ADD,
   opAt 2571 (.Dup ⟨0, by decide⟩),
   pushAt 2572 2 2080,
   opAt 2573 .MSTORE,
   opAt 2574 .LT,
   opAt 2575 .ISZERO,
   pushAt 2576 2 3136,
   opAt 2577 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .JUMPDEST,
   pushAt 2579 2 2080,
   opAt 2580 .MLOAD,
   opAt 2581 (.Dup ⟨0, by decide⟩),
   opAt 2582 .ISZERO,
   pushAt 2583 2 3120,
   opAt 2584 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2578 .JUMPDEST,
   pushAt 2579 2 2080,
   opAt 2580 .MLOAD,
   opAt 2581 (.Dup ⟨0, by decide⟩),
   opAt 2582 .ISZERO,
   pushAt 2583 2 3120,
   opAt 2584 .JUMPI,
   opAt 2585 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2586 .JUMPDEST,
   pushAt 2587 0 0,
   pushAt 2588 2 2784,
   opAt 2589 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2590 .JUMPDEST,
   opAt 2591 (.Dup ⟨0, by decide⟩),
   opAt 2592 .MLOAD,
   pushAt 2593 2 2112,
   opAt 2594 (.Dup ⟨2, by decide⟩),
   opAt 2595 .SUB,
   opAt 2596 .MLOAD,
   opAt 2597 (.Dup ⟨1, by decide⟩),
   opAt 2598 (.Dup ⟨1, by decide⟩),
   opAt 2599 .GT,
   opAt 2600 (.Swap ⟨1, by decide⟩),
   opAt 2601 .SUB,
   opAt 2602 (.Dup ⟨3, by decide⟩),
   opAt 2603 (.Dup ⟨1, by decide⟩),
   opAt 2604 .LT,
   opAt 2605 (.Swap ⟨0, by decide⟩),
   opAt 2606 (.Dup ⟨4, by decide⟩),
   opAt 2607 (.Swap ⟨0, by decide⟩),
   opAt 2608 .SUB,
   opAt 2609 (.Dup ⟨3, by decide⟩),
   opAt 2610 .MSTORE,
   opAt 2611 .OR,
   opAt 2612 (.Swap ⟨1, by decide⟩),
   opAt 2613 .POP,
   pushAt 2614 1 31,
   opAt 2615 .NOT,
   opAt 2616 .ADD,
   pushAt 2617 2 2111,
   opAt 2618 (.Dup ⟨1, by decide⟩),
   opAt 2619 .GT,
   pushAt 2620 2 3221,
   opAt 2621 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2622 .POP,
   pushAt 2623 2 2080,
   opAt 2624 .MLOAD,
   opAt 2625 .SUB,
   pushAt 2626 2 2080,
   opAt 2627 .MSTORE,
   pushAt 2628 2 3203,
   opAt 2629 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2517 .JUMPDEST,
   opAt 2518 .NOT,
   opAt 2519 .ADD,
   pushAt 2520 4 2691,
   opAt 2521 .JUMPDEST,
   opAt 2522 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2650 (.Dup ⟨0, by decide⟩),
   pushAt 2651 2 2112,
   pushAt 2652 2 512,
   opAt 2653 .MCOPY,
   opAt 2654 (.Dup ⟨0, by decide⟩),
   pushAt 2655 2 1280,
   pushAt 2656 2 1024,
   opAt 2657 .MCOPY,
   pushAt 2658 2 2396,
   opAt 2659 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2474 = true :=
  Artifact.isValidJumpDest_index 2018 (by rfl)


theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2508 = true :=
  Artifact.isValidJumpDest_index 2040 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2523 = true :=
  Artifact.isValidJumpDest_index 2048 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2691 = true :=
  Artifact.isValidJumpDest_index 2179 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3136 = true :=
  Artifact.isValidJumpDest_index 2527 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3142 = true :=
  Artifact.isValidJumpDest_index 2531 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3203 = true :=
  Artifact.isValidJumpDest_index 2578 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3221 = true :=
  Artifact.isValidJumpDest_index 2590 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3130 = true :=
  Artifact.isValidJumpDest_index 2523 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3215 = true :=
  Artifact.isValidJumpDest_index 2586 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3120 = true :=
  Artifact.isValidJumpDest_index 2517 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3274 = true :=
  Artifact.isValidJumpDest_index 2630 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
