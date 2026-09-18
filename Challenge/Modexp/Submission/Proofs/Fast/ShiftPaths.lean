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
   pushAt 2038 2 4229,
   opAt 2039 .JUMP]

def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2045 1 1,
   pushAt 2046 2 2752,
   opAt 2047 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2068 .POP,
   opAt 2069 .POP,
   pushAt 2070 0 0,
   opAt 2071 .MLOAD,
   opAt 2072 (.Dup ⟨0, by decide⟩),
   pushAt 2073 0 0,
   opAt 2074 .SUB,
   opAt 2075 (.Dup ⟨1, by decide⟩),
   opAt 2076 .AND,
   opAt 2077 (.Dup ⟨0, by decide⟩),
   pushAt 2078 2 1536,
   opAt 2079 .MSTORE,
   opAt 2080 (.Dup ⟨0, by decide⟩),
   opAt 2081 (.Dup ⟨2, by decide⟩),
   opAt 2082 .DIV,
   opAt 2083 (.Dup ⟨0, by decide⟩),
   pushAt 2084 2 1568,
   opAt 2085 .MSTORE,
   opAt 2086 (.Dup ⟨1, by decide⟩),
   opAt 2087 (.Dup ⟨0, by decide⟩),
   pushAt 2088 0 0,
   opAt 2089 .SUB,
   opAt 2090 .DIV,
   pushAt 2091 1 1,
   opAt 2092 .ADD,
   pushAt 2093 2 1600,
   opAt 2094 .MSTORE,
   opAt 2095 (.Dup ⟨0, by decide⟩),
   opAt 2096 (.Dup ⟨0, by decide⟩),
   pushAt 2097 0 0,
   opAt 2098 .SUB,
   opAt 2099 .MOD,
   pushAt 2100 2 1632,
   opAt 2101 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2102 (.Dup ⟨0, by decide⟩),
   pushAt 2103 1 3,
   opAt 2104 .MUL,
   pushAt 2105 1 2,
   opAt 2106 .XOR,
   opAt 2107 (.Dup ⟨0, by decide⟩),
   opAt 2108 (.Dup ⟨2, by decide⟩),
   opAt 2109 .MUL,
   pushAt 2110 1 2,
   opAt 2111 .SUB,
   opAt 2112 .MUL,
   opAt 2113 (.Dup ⟨0, by decide⟩),
   opAt 2114 (.Dup ⟨2, by decide⟩),
   opAt 2115 .MUL,
   pushAt 2116 1 2,
   opAt 2117 .SUB,
   opAt 2118 .MUL,
   opAt 2119 (.Dup ⟨0, by decide⟩),
   opAt 2120 (.Dup ⟨2, by decide⟩),
   opAt 2121 .MUL,
   pushAt 2122 1 2,
   opAt 2123 .SUB,
   opAt 2124 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2125 (.Dup ⟨0, by decide⟩),
   opAt 2126 (.Dup ⟨2, by decide⟩),
   opAt 2127 .MUL,
   pushAt 2128 1 2,
   opAt 2129 .SUB,
   opAt 2130 .MUL,
   opAt 2131 (.Dup ⟨0, by decide⟩),
   opAt 2132 (.Dup ⟨2, by decide⟩),
   opAt 2133 .MUL,
   pushAt 2134 1 2,
   opAt 2135 .SUB,
   opAt 2136 .MUL,
   opAt 2137 (.Dup ⟨0, by decide⟩),
   opAt 2138 (.Dup ⟨2, by decide⟩),
   opAt 2139 .MUL,
   pushAt 2140 1 2,
   opAt 2141 .SUB,
   opAt 2142 .MUL,
   pushAt 2143 2 1664,
   opAt 2144 .MSTORE,
   opAt 2145 .POP,
   opAt 2146 .POP,
   opAt 2147 .POP,
   opAt 2148 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2178 .JUMPDEST,
   opAt 2179 (.Dup ⟨0, by decide⟩),
   opAt 2180 .ISZERO,
   pushAt 2181 2 3274,
   opAt 2182 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2183 (.Dup ⟨1, by decide⟩),
   pushAt 2184 2 2112,
   pushAt 2185 2 2080,
   opAt 2186 .MCOPY,
   pushAt 2187 0 0,
   pushAt 2188 2 2784,
   opAt 2189 .MLOAD,
   opAt 2190 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2191 2 2080,
   opAt 2192 .MLOAD,
   pushAt 2193 2 1536,
   opAt 2194 .MLOAD,
   opAt 2195 (.Dup ⟨1, by decide⟩),
   opAt 2196 .DIV,
   opAt 2197 (.Swap ⟨0, by decide⟩),
   pushAt 2198 2 1600,
   opAt 2199 .MLOAD,
   opAt 2200 .MUL,
   pushAt 2201 2 1536,
   opAt 2202 .MLOAD,
   pushAt 2203 2 2112,
   opAt 2204 .MLOAD,
   opAt 2205 .DIV,
   opAt 2206 .ADD,
   pushAt 2207 2 1568,
   opAt 2208 .MLOAD,
   opAt 2209 (.Dup ⟨0, by decide⟩),
   pushAt 2210 2 1632,
   opAt 2211 .MLOAD,
   opAt 2212 (.Dup ⟨4, by decide⟩),
   opAt 2213 .MULMOD,
   opAt 2214 (.Dup ⟨2, by decide⟩),
   opAt 2215 .ADDMOD,
   opAt 2216 (.Swap ⟨0, by decide⟩),
   opAt 2217 .SUB,
   pushAt 2218 2 1664,
   opAt 2219 .MLOAD,
   opAt 2220 .MUL,
   opAt 2221 (.Dup ⟨0, by decide⟩),
   pushAt 2222 0 0,
   opAt 2223 .MLOAD,
   opAt 2224 .MUL,
   pushAt 2225 2 2112,
   opAt 2226 .MLOAD,
   opAt 2227 .SUB,
   pushAt 2228 1 32,
   opAt 2229 .MLOAD,
   pushAt 2230 1 128,
   opAt 2231 .SHR,
   opAt 2232 (.Dup ⟨2, by decide⟩),
   pushAt 2233 1 128,
   opAt 2234 .SHR,
   opAt 2235 .MUL,
   opAt 2236 .GT,
   opAt 2237 (.Swap ⟨0, by decide⟩),
   opAt 2238 .SUB,
   opAt 2239 (.Swap ⟨0, by decide⟩),
   pushAt 2240 2 1568,
   opAt 2241 .MLOAD,
   opAt 2242 .GT,
   opAt 2243 .ISZERO,
   pushAt 2244 0 0,
   opAt 2245 .SUB,
   opAt 2246 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2497 2 2080,
   opAt 2498 .MLOAD,
   opAt 2499 (.Dup ⟨1, by decide⟩),
   opAt 2500 .ADD,
   opAt 2501 (.Dup ⟨0, by decide⟩),
   opAt 2502 (.Swap ⟨1, by decide⟩),
   opAt 2503 .GT,
   opAt 2504 (.Dup ⟨1, by decide⟩),
   opAt 2505 (.Dup ⟨3, by decide⟩),
   opAt 2506 .GT,
   opAt 2507 .GT,
   opAt 2508 (.Swap ⟨1, by decide⟩),
   opAt 2509 (.Swap ⟨0, by decide⟩),
   opAt 2510 .SUB,
   opAt 2511 (.Dup ⟨0, by decide⟩),
   pushAt 2512 2 2080,
   opAt 2513 .MSTORE,
   pushAt 2514 4 3130,
   opAt 2515 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2521 .JUMPDEST,
   opAt 2522 .ISZERO,
   pushAt 2523 2 3215,
   opAt 2524 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2525 .JUMPDEST,
   pushAt 2526 0 0,
   pushAt 2527 2 2784,
   opAt 2528 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2529 .JUMPDEST,
   opAt 2530 (.Dup ⟨0, by decide⟩),
   opAt 2531 .MLOAD,
   pushAt 2532 3 2112,
   opAt 2533 (.Dup ⟨2, by decide⟩),
   opAt 2534 .SUB,
   opAt 2535 .MLOAD,
   opAt 2536 (.Dup ⟨1, by decide⟩),
   opAt 2537 .ADD,
   opAt 2538 (.Swap ⟨0, by decide⟩),
   opAt 2539 (.Dup ⟨1, by decide⟩),
   opAt 2540 .LT,
   opAt 2541 (.Swap ⟨0, by decide⟩),
   opAt 2542 (.Dup ⟨3, by decide⟩),
   opAt 2543 .ADD,
   opAt 2544 (.Swap ⟨2, by decide⟩),
   opAt 2545 (.Dup ⟨3, by decide⟩),
   opAt 2546 .LT,
   opAt 2547 .OR,
   opAt 2548 (.Swap ⟨1, by decide⟩),
   opAt 2549 (.Dup ⟨1, by decide⟩),
   opAt 2550 .MSTORE,
   pushAt 2551 1 31,
   opAt 2552 .NOT,
   opAt 2553 .ADD,
   pushAt 2554 2 2111,
   opAt 2555 (.Dup ⟨1, by decide⟩),
   opAt 2556 .GT,
   pushAt 2557 2 3142,
   opAt 2558 .JUMPI,
   opAt 2559 .JUMPDEST,
   opAt 2560 .JUMPDEST,
   opAt 2561 .JUMPDEST,
   opAt 2562 .JUMPDEST,
   opAt 2563 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2564 .POP,
   pushAt 2565 2 2080,
   opAt 2566 .MLOAD,
   opAt 2567 (.Dup ⟨1, by decide⟩),
   opAt 2568 .ADD,
   opAt 2569 (.Dup ⟨0, by decide⟩),
   pushAt 2570 2 2080,
   opAt 2571 .MSTORE,
   opAt 2572 .LT,
   opAt 2573 .ISZERO,
   pushAt 2574 2 3136,
   opAt 2575 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2576 .JUMPDEST,
   pushAt 2577 2 2080,
   opAt 2578 .MLOAD,
   opAt 2579 (.Dup ⟨0, by decide⟩),
   opAt 2580 .ISZERO,
   pushAt 2581 2 3120,
   opAt 2582 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2576 .JUMPDEST,
   pushAt 2577 2 2080,
   opAt 2578 .MLOAD,
   opAt 2579 (.Dup ⟨0, by decide⟩),
   opAt 2580 .ISZERO,
   pushAt 2581 2 3120,
   opAt 2582 .JUMPI,
   opAt 2583 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2584 .JUMPDEST,
   pushAt 2585 0 0,
   pushAt 2586 2 2784,
   opAt 2587 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2588 .JUMPDEST,
   opAt 2589 (.Dup ⟨0, by decide⟩),
   opAt 2590 .MLOAD,
   pushAt 2591 2 2112,
   opAt 2592 (.Dup ⟨2, by decide⟩),
   opAt 2593 .SUB,
   opAt 2594 .MLOAD,
   opAt 2595 (.Dup ⟨1, by decide⟩),
   opAt 2596 (.Dup ⟨1, by decide⟩),
   opAt 2597 .GT,
   opAt 2598 (.Swap ⟨1, by decide⟩),
   opAt 2599 .SUB,
   opAt 2600 (.Dup ⟨3, by decide⟩),
   opAt 2601 (.Dup ⟨1, by decide⟩),
   opAt 2602 .LT,
   opAt 2603 (.Swap ⟨0, by decide⟩),
   opAt 2604 (.Dup ⟨4, by decide⟩),
   opAt 2605 (.Swap ⟨0, by decide⟩),
   opAt 2606 .SUB,
   opAt 2607 (.Dup ⟨3, by decide⟩),
   opAt 2608 .MSTORE,
   opAt 2609 .OR,
   opAt 2610 (.Swap ⟨1, by decide⟩),
   opAt 2611 .POP,
   pushAt 2612 1 31,
   opAt 2613 .NOT,
   opAt 2614 .ADD,
   pushAt 2615 2 2111,
   opAt 2616 (.Dup ⟨1, by decide⟩),
   opAt 2617 .GT,
   pushAt 2618 2 3221,
   opAt 2619 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2620 .POP,
   pushAt 2621 2 2080,
   opAt 2622 .MLOAD,
   opAt 2623 .SUB,
   pushAt 2624 2 2080,
   opAt 2625 .MSTORE,
   pushAt 2626 2 3203,
   opAt 2627 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2516 .JUMPDEST,
   opAt 2517 .NOT,
   opAt 2518 .ADD,
   pushAt 2519 5 2691,
   opAt 2520 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2648 (.Dup ⟨0, by decide⟩),
   pushAt 2649 2 2112,
   pushAt 2650 2 512,
   opAt 2651 .MCOPY,
   opAt 2652 (.Dup ⟨0, by decide⟩),
   pushAt 2653 2 1280,
   pushAt 2654 2 1024,
   opAt 2655 .MCOPY,
   pushAt 2656 2 2396,
   opAt 2657 .JUMP]

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
  Artifact.isValidJumpDest_index 2178 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3136 = true :=
  Artifact.isValidJumpDest_index 2525 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3142 = true :=
  Artifact.isValidJumpDest_index 2529 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3203 = true :=
  Artifact.isValidJumpDest_index 2576 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3221 = true :=
  Artifact.isValidJumpDest_index 2588 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3130 = true :=
  Artifact.isValidJumpDest_index 2521 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3215 = true :=
  Artifact.isValidJumpDest_index 2584 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3120 = true :=
  Artifact.isValidJumpDest_index 2516 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3274 = true :=
  Artifact.isValidJumpDest_index 2628 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
