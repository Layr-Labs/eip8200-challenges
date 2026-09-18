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
  [opAt 2016 .JUMPDEST,
   opAt 2017 (.Dup ⟨0, by decide⟩),
   opAt 2018 (.Dup ⟨3, by decide⟩),
   opAt 2019 .EQ,
   pushAt 2020 0 0,
   opAt 2021 .MLOAD,
   pushAt 2022 1 255,
   opAt 2023 .SHR,
   opAt 2024 .AND,
   opAt 2025 .ISZERO,
   pushAt 2026 2 800,
   opAt 2027 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2028 (.Dup ⟨0, by decide⟩),
   pushAt 2029 1 96,
   pushAt 2030 2 2112,
   opAt 2031 .CALLDATACOPY,
   pushAt 2032 0 0,
   pushAt 2033 2 2080,
   opAt 2034 .MSTORE,
   pushAt 2035 2 2508,
   pushAt 2036 2 4229,
   opAt 2037 .JUMP]

def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2043 1 1,
   pushAt 2044 2 2752,
   opAt 2045 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2067 .POP,
   opAt 2068 .POP,
   pushAt 2069 0 0,
   opAt 2070 .MLOAD,
   opAt 2071 (.Dup ⟨0, by decide⟩),
   pushAt 2072 0 0,
   opAt 2073 .SUB,
   opAt 2074 (.Dup ⟨1, by decide⟩),
   opAt 2075 .AND,
   opAt 2076 (.Dup ⟨0, by decide⟩),
   pushAt 2077 2 1536,
   opAt 2078 .MSTORE,
   opAt 2079 (.Dup ⟨0, by decide⟩),
   opAt 2080 (.Dup ⟨2, by decide⟩),
   opAt 2081 .DIV,
   opAt 2082 (.Dup ⟨0, by decide⟩),
   pushAt 2083 2 1568,
   opAt 2084 .MSTORE,
   opAt 2085 (.Dup ⟨1, by decide⟩),
   opAt 2086 (.Dup ⟨0, by decide⟩),
   pushAt 2087 0 0,
   opAt 2088 .SUB,
   opAt 2089 .DIV,
   pushAt 2090 1 1,
   opAt 2091 .ADD,
   pushAt 2092 2 1600,
   opAt 2093 .MSTORE,
   opAt 2094 (.Dup ⟨0, by decide⟩),
   opAt 2095 (.Dup ⟨0, by decide⟩),
   pushAt 2096 0 0,
   opAt 2097 .SUB,
   opAt 2098 .MOD,
   pushAt 2099 2 1632,
   opAt 2100 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2101 (.Dup ⟨0, by decide⟩),
   pushAt 2102 1 3,
   opAt 2103 .MUL,
   pushAt 2104 1 2,
   opAt 2105 .XOR,
   opAt 2106 (.Dup ⟨0, by decide⟩),
   opAt 2107 (.Dup ⟨2, by decide⟩),
   opAt 2108 .MUL,
   pushAt 2109 1 2,
   opAt 2110 .SUB,
   opAt 2111 .MUL,
   opAt 2112 (.Dup ⟨0, by decide⟩),
   opAt 2113 (.Dup ⟨2, by decide⟩),
   opAt 2114 .MUL,
   pushAt 2115 1 2,
   opAt 2116 .SUB,
   opAt 2117 .MUL,
   opAt 2118 (.Dup ⟨0, by decide⟩),
   opAt 2119 (.Dup ⟨2, by decide⟩),
   opAt 2120 .MUL,
   pushAt 2121 1 2,
   opAt 2122 .SUB,
   opAt 2123 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2124 (.Dup ⟨0, by decide⟩),
   opAt 2125 (.Dup ⟨2, by decide⟩),
   opAt 2126 .MUL,
   pushAt 2127 1 2,
   opAt 2128 .SUB,
   opAt 2129 .MUL,
   opAt 2130 (.Dup ⟨0, by decide⟩),
   opAt 2131 (.Dup ⟨2, by decide⟩),
   opAt 2132 .MUL,
   pushAt 2133 1 2,
   opAt 2134 .SUB,
   opAt 2135 .MUL,
   opAt 2136 (.Dup ⟨0, by decide⟩),
   opAt 2137 (.Dup ⟨2, by decide⟩),
   opAt 2138 .MUL,
   pushAt 2139 1 2,
   opAt 2140 .SUB,
   opAt 2141 .MUL,
   pushAt 2142 2 1664,
   opAt 2143 .MSTORE,
   opAt 2144 .POP,
   opAt 2145 .POP,
   opAt 2146 .POP,
   opAt 2147 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2177 .JUMPDEST,
   opAt 2178 (.Dup ⟨0, by decide⟩),
   opAt 2179 .ISZERO,
   pushAt 2180 2 3274,
   opAt 2181 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2182 (.Dup ⟨1, by decide⟩),
   pushAt 2183 2 2112,
   pushAt 2184 2 2080,
   opAt 2185 .MCOPY,
   pushAt 2186 0 0,
   pushAt 2187 2 2784,
   opAt 2188 .MLOAD,
   opAt 2189 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2190 2 2080,
   opAt 2191 .MLOAD,
   pushAt 2192 2 1536,
   opAt 2193 .MLOAD,
   opAt 2194 (.Dup ⟨1, by decide⟩),
   opAt 2195 .DIV,
   opAt 2196 (.Swap ⟨0, by decide⟩),
   pushAt 2197 2 1600,
   opAt 2198 .MLOAD,
   opAt 2199 .MUL,
   pushAt 2200 2 1536,
   opAt 2201 .MLOAD,
   pushAt 2202 2 2112,
   opAt 2203 .MLOAD,
   opAt 2204 .DIV,
   opAt 2205 .ADD,
   pushAt 2206 2 1568,
   opAt 2207 .MLOAD,
   opAt 2208 (.Dup ⟨0, by decide⟩),
   pushAt 2209 2 1632,
   opAt 2210 .MLOAD,
   opAt 2211 (.Dup ⟨4, by decide⟩),
   opAt 2212 .MULMOD,
   opAt 2213 (.Dup ⟨2, by decide⟩),
   opAt 2214 .ADDMOD,
   opAt 2215 (.Swap ⟨0, by decide⟩),
   opAt 2216 .SUB,
   pushAt 2217 2 1664,
   opAt 2218 .MLOAD,
   opAt 2219 .MUL,
   opAt 2220 (.Dup ⟨0, by decide⟩),
   pushAt 2221 0 0,
   opAt 2222 .MLOAD,
   opAt 2223 .MUL,
   pushAt 2224 2 2112,
   opAt 2225 .MLOAD,
   opAt 2226 .SUB,
   pushAt 2227 1 32,
   opAt 2228 .MLOAD,
   pushAt 2229 1 128,
   opAt 2230 .SHR,
   opAt 2231 (.Dup ⟨2, by decide⟩),
   pushAt 2232 1 128,
   opAt 2233 .SHR,
   opAt 2234 .MUL,
   opAt 2235 .GT,
   opAt 2236 (.Swap ⟨0, by decide⟩),
   opAt 2237 .SUB,
   opAt 2238 (.Swap ⟨0, by decide⟩),
   pushAt 2239 2 1568,
   opAt 2240 .MLOAD,
   opAt 2241 .GT,
   opAt 2242 .ISZERO,
   pushAt 2243 0 0,
   opAt 2244 .SUB,
   opAt 2245 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2496 2 2080,
   opAt 2497 .MLOAD,
   opAt 2498 (.Dup ⟨1, by decide⟩),
   opAt 2499 .ADD,
   opAt 2500 (.Dup ⟨0, by decide⟩),
   opAt 2501 (.Swap ⟨1, by decide⟩),
   opAt 2502 .GT,
   opAt 2503 (.Dup ⟨1, by decide⟩),
   opAt 2504 (.Dup ⟨3, by decide⟩),
   opAt 2505 .GT,
   opAt 2506 .GT,
   opAt 2507 (.Swap ⟨1, by decide⟩),
   opAt 2508 (.Swap ⟨0, by decide⟩),
   opAt 2509 .SUB,
   opAt 2510 (.Dup ⟨0, by decide⟩),
   pushAt 2511 2 2080,
   opAt 2512 .MSTORE,
   pushAt 2513 4 3130,
   opAt 2514 .JUMPI]

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
  [opAt 2515 .JUMPDEST,
   opAt 2516 .NOT,
   opAt 2517 .ADD,
   pushAt 2518 4 2691,
   opAt 2519 .JUMPDEST,
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
  Artifact.isValidJumpDest_index 2016 (by rfl)


theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2508 = true :=
  Artifact.isValidJumpDest_index 2038 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2523 = true :=
  Artifact.isValidJumpDest_index 2046 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2691 = true :=
  Artifact.isValidJumpDest_index 2177 (by rfl)

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
  Artifact.isValidJumpDest_index 2515 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3274 = true :=
  Artifact.isValidJumpDest_index 2628 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
