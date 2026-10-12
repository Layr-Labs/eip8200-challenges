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
  [opAt 1992 .JUMPDEST,
   opAt 1993 (.Dup ⟨0, by decide⟩),
   opAt 1994 (.Dup ⟨3, by decide⟩),
   opAt 1995 .EQ,
   pushAt 1996 0 0,
   opAt 1997 .MLOAD,
   pushAt 1998 1 255,
   opAt 1999 .SHR,
   opAt 2000 .AND,
   opAt 2001 .ISZERO,
   pushAt 2002 2 790,
   opAt 2003 .JUMPI]

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
  [opAt 2004 (.Dup ⟨0, by decide⟩),
   pushAt 2005 1 96,
   pushAt 2006 2 2112,
   opAt 2007 .CALLDATACOPY,
   pushAt 2008 2 2574,
   pushAt 2009 2 4308,
   opAt 2010 .JUMP]


/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2016 1 1,
   pushAt 2017 2 2752,
   opAt 2018 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2040 .POP,
   opAt 2041 .POP,
   pushAt 2042 0 0,
   opAt 2043 .MLOAD,
   opAt 2044 (.Dup ⟨0, by decide⟩),
   pushAt 2045 0 0,
   opAt 2046 .SUB,
   opAt 2047 (.Dup ⟨1, by decide⟩),
   opAt 2048 .AND,
   opAt 2049 (.Dup ⟨0, by decide⟩),
   pushAt 2050 2 1536,
   opAt 2051 .MSTORE,
   opAt 2052 (.Dup ⟨0, by decide⟩),
   opAt 2053 (.Dup ⟨2, by decide⟩),
   opAt 2054 .DIV,
   opAt 2055 (.Dup ⟨0, by decide⟩),
   pushAt 2056 2 1568,
   opAt 2057 .MSTORE,
   opAt 2058 (.Dup ⟨1, by decide⟩),
   opAt 2059 (.Dup ⟨0, by decide⟩),
   pushAt 2060 0 0,
   opAt 2061 .SUB,
   opAt 2062 .DIV,
   pushAt 2063 1 1,
   opAt 2064 .ADD,
   pushAt 2065 2 1600,
   opAt 2066 .MSTORE,
   opAt 2067 (.Dup ⟨0, by decide⟩),
   opAt 2068 (.Dup ⟨0, by decide⟩),
   pushAt 2069 0 0,
   opAt 2070 .SUB,
   opAt 2071 .MOD,
   pushAt 2072 2 1632,
   opAt 2073 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2074 (.Dup ⟨0, by decide⟩),
   pushAt 2075 1 3,
   opAt 2076 .MUL,
   pushAt 2077 1 2,
   opAt 2078 .XOR,
   opAt 2079 (.Dup ⟨0, by decide⟩),
   opAt 2080 (.Dup ⟨2, by decide⟩),
   opAt 2081 .MUL,
   pushAt 2082 1 2,
   opAt 2083 .SUB,
   opAt 2084 .MUL,
   opAt 2085 (.Dup ⟨0, by decide⟩),
   opAt 2086 (.Dup ⟨2, by decide⟩),
   opAt 2087 .MUL,
   pushAt 2088 1 2,
   opAt 2089 .SUB,
   opAt 2090 .MUL,
   opAt 2091 (.Dup ⟨0, by decide⟩),
   opAt 2092 (.Dup ⟨2, by decide⟩),
   opAt 2093 .MUL,
   pushAt 2094 1 2,
   opAt 2095 .SUB,
   opAt 2096 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2097 (.Dup ⟨0, by decide⟩),
   opAt 2098 (.Dup ⟨2, by decide⟩),
   opAt 2099 .MUL,
   pushAt 2100 1 2,
   opAt 2101 .SUB,
   opAt 2102 .MUL,
   opAt 2103 (.Dup ⟨0, by decide⟩),
   opAt 2104 (.Dup ⟨2, by decide⟩),
   opAt 2105 .MUL,
   pushAt 2106 1 2,
   opAt 2107 .SUB,
   opAt 2108 .MUL,
   opAt 2109 (.Dup ⟨0, by decide⟩),
   opAt 2110 (.Dup ⟨2, by decide⟩),
   opAt 2111 .MUL,
   pushAt 2112 1 2,
   opAt 2113 .SUB,
   opAt 2114 .MUL,
   pushAt 2115 2 1664,
   opAt 2116 .MSTORE,
   opAt 2117 .POP,
   opAt 2118 .POP,
   opAt 2119 .POP,
   pushAt 2120 0 0,
   pushAt 2121 0 0,
   opAt 2122 (.Dup ⟨4, by decide⟩),
   opAt 2123 (.Dup ⟨4, by decide⟩),
   opAt 2124 (.Dup ⟨7, by decide⟩),
   pushAt 2125 2 1536,
   opAt 2126 .MLOAD,
   pushAt 2127 2 1568,
   opAt 2128 .MLOAD,
   pushAt 2129 2 1664,
   opAt 2130 .MLOAD,
   pushAt 2131 2 1632,
   opAt 2132 .MLOAD,
   pushAt 2133 2 1504,
   opAt 2134 .MLOAD,
   pushAt 2135 2 1472,
   opAt 2136 .MLOAD,
   pushAt 2137 2 1440,
   opAt 2138 .MLOAD,
   pushAt 2139 2 1408,
   opAt 2140 .MLOAD,
   pushAt 2141 2 1376,
   opAt 2142 .MLOAD,
   pushAt 2143 2 1344,
   opAt 2144 .MLOAD,
   pushAt 2145 2 1312,
   opAt 2146 .MLOAD,
   opAt 2147 (.Dup ⟨12, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2180 .JUMPDEST,
   opAt 2181 (.Dup ⟨0, by decide⟩),
   opAt 2182 .ISZERO,
   pushAt 2183 2 3346,
   opAt 2184 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2185 (.Dup ⟨15, by decide⟩),
   pushAt 2186 2 2112,
   pushAt 2187 2 2080,
   opAt 2188 .MCOPY,
   pushAt 2189 0 0,
   pushAt 2190 2 2784,
   opAt 2191 .MLOAD,
   opAt 2192 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2193 2 2080,
   opAt 2194 .MLOAD,
   opAt 2195 (.Dup ⟨13, by decide⟩),
   opAt 2196 (.Dup ⟨1, by decide⟩),
   opAt 2197 .DIV,
   opAt 2198 (.Swap ⟨0, by decide⟩),
   pushAt 2199 2 1600,
   opAt 2200 .MLOAD,
   opAt 2201 .MUL,
   opAt 2202 (.Dup ⟨14, by decide⟩),
   pushAt 2203 2 2112,
   opAt 2204 .MLOAD,
   opAt 2205 .DIV,
   opAt 2206 .ADD,
   opAt 2207 (.Dup ⟨13, by decide⟩),
   opAt 2208 (.Dup ⟨0, by decide⟩),
   opAt 2209 (.Dup ⟨13, by decide⟩),
   opAt 2210 (.Dup ⟨4, by decide⟩),
   opAt 2211 .MULMOD,
   opAt 2212 (.Dup ⟨2, by decide⟩),
   opAt 2213 .ADDMOD,
   opAt 2214 (.Swap ⟨0, by decide⟩),
   opAt 2215 .SUB,
   opAt 2216 (.Dup ⟨12, by decide⟩),
   opAt 2217 .MUL,
   opAt 2218 (.Dup ⟨0, by decide⟩),
   pushAt 2219 0 0,
   opAt 2220 .MLOAD,
   opAt 2221 .MUL,
   pushAt 2222 2 2112,
   opAt 2223 .MLOAD,
   opAt 2224 .SUB,
   pushAt 2225 1 32,
   opAt 2226 .MLOAD,
   pushAt 2227 1 128,
   opAt 2228 .SHR,
   opAt 2229 (.Dup ⟨2, by decide⟩),
   pushAt 2230 1 128,
   opAt 2231 .SHR,
   opAt 2232 .MUL,
   opAt 2233 .GT,
   opAt 2234 (.Swap ⟨0, by decide⟩),
   opAt 2235 .SUB,
   pushAt 2236 0 0,
   opAt 2237 .NOT,
   opAt 2238 (.Swap ⟨1, by decide⟩),
   opAt 2239 (.Dup ⟨14, by decide⟩),
   opAt 2240 .GT,
   opAt 2241 .ISZERO,
   pushAt 2242 0 0,
   opAt 2243 .SUB,
   opAt 2244 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2466 5 2080,
   opAt 2467 .MLOAD,
   opAt 2468 (.Dup ⟨1, by decide⟩),
   opAt 2469 .ADD,
   opAt 2470 (.Dup ⟨0, by decide⟩),
   opAt 2471 (.Swap ⟨1, by decide⟩),
   opAt 2472 .GT,
   opAt 2473 (.Dup ⟨1, by decide⟩),
   opAt 2474 (.Dup ⟨3, by decide⟩),
   opAt 2475 .GT,
   opAt 2476 .GT,
   opAt 2477 (.Swap ⟨2, by decide⟩),
   opAt 2478 .POP,
   opAt 2479 .SUB,
   opAt 2480 (.Dup ⟨0, by decide⟩),
   pushAt 2481 2 2080,
   opAt 2482 .MSTORE,
   opAt 2483 (.Dup ⟨1, by decide⟩),
   opAt 2484 .OR,
   pushAt 2485 2 3208,
   opAt 2486 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2495 .JUMPDEST,
   opAt 2496 .ISZERO,
   pushAt 2497 2 3287,
   opAt 2498 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2499 .JUMPDEST,
   pushAt 2500 0 0,
   pushAt 2501 2 2784,
   opAt 2502 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2503 .JUMPDEST,
   opAt 2504 (.Dup ⟨0, by decide⟩),
   opAt 2505 .MLOAD,
   pushAt 2506 2 2112,
   opAt 2507 (.Dup ⟨2, by decide⟩),
   opAt 2508 .SUB,
   opAt 2509 .MLOAD,
   opAt 2510 (.Dup ⟨1, by decide⟩),
   opAt 2511 .ADD,
   opAt 2512 (.Swap ⟨0, by decide⟩),
   opAt 2513 (.Dup ⟨1, by decide⟩),
   opAt 2514 .LT,
   opAt 2515 (.Swap ⟨0, by decide⟩),
   opAt 2516 (.Dup ⟨3, by decide⟩),
   opAt 2517 .ADD,
   opAt 2518 (.Swap ⟨2, by decide⟩),
   opAt 2519 (.Dup ⟨3, by decide⟩),
   opAt 2520 .LT,
   opAt 2521 .OR,
   opAt 2522 (.Swap ⟨1, by decide⟩),
   opAt 2523 (.Dup ⟨1, by decide⟩),
   opAt 2524 .MSTORE,
   pushAt 2525 1 31,
   opAt 2526 .NOT,
   opAt 2527 .ADD,
   pushAt 2528 2 2111,
   opAt 2529 (.Dup ⟨1, by decide⟩),
   opAt 2530 .GT,
   pushAt 2531 2 3220,
   opAt 2532 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2533 .POP,
   pushAt 2534 2 2080,
   opAt 2535 .MLOAD,
   opAt 2536 (.Dup ⟨1, by decide⟩),
   opAt 2537 .ADD,
   opAt 2538 (.Dup ⟨0, by decide⟩),
   pushAt 2539 2 2080,
   opAt 2540 .MSTORE,
   opAt 2541 .LT,
   opAt 2542 .ISZERO,
   pushAt 2543 2 3214,
   opAt 2544 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2545 .JUMPDEST,
   pushAt 2546 2 2080,
   opAt 2547 .MLOAD,
   opAt 2548 (.Dup ⟨0, by decide⟩),
   opAt 2549 .ISZERO,
   pushAt 2550 2 3198,
   opAt 2551 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2545 .JUMPDEST,
   pushAt 2546 2 2080,
   opAt 2547 .MLOAD,
   opAt 2548 (.Dup ⟨0, by decide⟩),
   opAt 2549 .ISZERO,
   pushAt 2550 2 3198,
   opAt 2551 .JUMPI,
   opAt 2552 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2553 .JUMPDEST,
   pushAt 2554 0 0,
   pushAt 2555 2 2784,
   opAt 2556 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2557 .JUMPDEST,
   opAt 2558 (.Dup ⟨0, by decide⟩),
   opAt 2559 .MLOAD,
   pushAt 2560 2 2112,
   opAt 2561 (.Dup ⟨2, by decide⟩),
   opAt 2562 .SUB,
   opAt 2563 .MLOAD,
   opAt 2564 (.Dup ⟨1, by decide⟩),
   opAt 2565 (.Dup ⟨1, by decide⟩),
   opAt 2566 .GT,
   opAt 2567 (.Swap ⟨1, by decide⟩),
   opAt 2568 .SUB,
   opAt 2569 (.Dup ⟨3, by decide⟩),
   opAt 2570 (.Dup ⟨1, by decide⟩),
   opAt 2571 .LT,
   opAt 2572 (.Swap ⟨0, by decide⟩),
   opAt 2573 (.Dup ⟨4, by decide⟩),
   opAt 2574 (.Swap ⟨0, by decide⟩),
   opAt 2575 .SUB,
   opAt 2576 (.Dup ⟨3, by decide⟩),
   opAt 2577 .MSTORE,
   opAt 2578 .OR,
   opAt 2579 (.Swap ⟨1, by decide⟩),
   opAt 2580 .POP,
   pushAt 2581 1 31,
   opAt 2582 .NOT,
   opAt 2583 .ADD,
   pushAt 2584 2 2111,
   opAt 2585 (.Dup ⟨1, by decide⟩),
   opAt 2586 .GT,
   pushAt 2587 2 3284,
   opAt 2588 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2589 .POP,
   pushAt 2590 2 2080,
   opAt 2591 .MLOAD,
   opAt 2592 .SUB,
   pushAt 2593 2 2080,
   opAt 2594 .MSTORE,
   pushAt 2595 2 3266,
   opAt 2596 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), jump straight to the loop head (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2487 .JUMPDEST,
   opAt 2488 .NOT,
   opAt 2489 .ADD,
   pushAt 2490 2 2811,
   opAt 2491 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2617 2 2441,
   opAt 2618 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2545 = true :=
  Artifact.isValidJumpDest_index 1992 (by rfl)

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
  Artifact.isValidJumpDest_index 2011 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2589 = true :=
  Artifact.isValidJumpDest_index 2019 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2811 = true :=
  Artifact.isValidJumpDest_index 2180 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3214 = true :=
  Artifact.isValidJumpDest_index 2499 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3220 = true :=
  Artifact.isValidJumpDest_index 2503 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3275 = true :=
  Artifact.isValidJumpDest_index 2545 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3293 = true :=
  Artifact.isValidJumpDest_index 2557 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3208 = true :=
  Artifact.isValidJumpDest_index 2495 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3287 = true :=
  Artifact.isValidJumpDest_index 2553 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3198 = true :=
  Artifact.isValidJumpDest_index 2487 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3346 = true :=
  Artifact.isValidJumpDest_index 2597 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5444 = true :=
  Artifact.isValidJumpDest_index 4282 (by rfl)

theorem jumpDest3378 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3378 = true :=
  Artifact.isValidJumpDest_index 2616 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2899 + 133·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2148 (.Dup ⟨0, by decide⟩),
   pushAt 2149 1 4,
   opAt 2150 .EQ,
   pushAt 2151 1 133,
   opAt 2152 .MUL,
   pushAt 2153 2 2899,
   opAt 2154 .ADD,
   pushAt 2155 2 1698,
   opAt 2156 .MSTORE,
   opAt 2157 (.Dup ⟨12, by decide⟩),
   pushAt 2158 1 1,
   opAt 2159 .EQ,
   pushAt 2160 2 2816,
   opAt 2161 .MLOAD,
   opAt 2162 .CALLDATALOAD,
   pushAt 2163 0 0,
   opAt 2164 .BYTE,
   pushAt 2165 1 3,
   opAt 2166 .EQ,
   opAt 2167 .AND,
   opAt 2168 (.Dup ⟨1, by decide⟩),
   pushAt 2169 1 3,
   opAt 2170 .AND,
   opAt 2171 .ISZERO,
   opAt 2172 .AND,
   opAt 2173 (.Dup ⟨0, by decide⟩),
   pushAt 2174 2 1760,
   opAt 2175 .MSTORE,
   opAt 2176 .SHR,
   pushAt 2177 2 1698,
   opAt 2178 .MLOAD,
   opAt 2179 (.Swap ⟨0, by decide⟩)]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3377). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2597 .JUMPDEST,
   opAt 2598 .POP,
   pushAt 2599 2 1760,
   opAt 2600 .MLOAD,
   opAt 2601 .ISZERO,
   pushAt 2602 2 5444,
   opAt 2603 .JUMPI]

/-- The cleanup tail (pcs 5444-5465): seventeen `POP`s drop the riding slots,
restoring the bare outer frame, then jump to the done stub. -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4282 .JUMPDEST,
   opAt 4283 .POP,
   opAt 4284 .POP,
   opAt 4285 .POP,
   opAt 4286 .POP,
   opAt 4287 .POP,
   opAt 4288 .POP,
   opAt 4289 .POP,
   opAt 4290 .POP,
   opAt 4291 .POP,
   opAt 4292 .POP,
   opAt 4293 .POP,
   opAt 4294 .POP,
   opAt 4295 .POP,
   opAt 4296 .POP,
   opAt 4297 .POP,
   opAt 4298 .POP,
   opAt 4299 .POP,
   pushAt 4300 2 3378,
   opAt 4301 .JUMP]

/-- The done stub (pcs 3378-3382): jump to the exponent phase's dispatcher. -/
def blk3378 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2616 .JUMPDEST,
   pushAt 2617 2 2441,
   opAt 2618 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
