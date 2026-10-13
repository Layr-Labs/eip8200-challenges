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
  [pushAt 2016 2 2752,
   opAt 2017 .MLOAD,
   pushAt 2018 1 1]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2036 .JUMPDEST,
   opAt 2037 .POP,
   opAt 2038 .POP,
   pushAt 2039 3 0,
   opAt 2040 .MLOAD,
   opAt 2041 (.Dup ⟨0, by decide⟩),
   pushAt 2042 0 0,
   opAt 2043 .SUB,
   opAt 2044 (.Dup ⟨1, by decide⟩),
   opAt 2045 .AND,
   opAt 2046 (.Dup ⟨0, by decide⟩),
   pushAt 2047 2 1536,
   opAt 2048 .MSTORE,
   opAt 2049 (.Dup ⟨0, by decide⟩),
   opAt 2050 (.Dup ⟨2, by decide⟩),
   opAt 2051 .DIV,
   opAt 2052 (.Dup ⟨0, by decide⟩),
   pushAt 2053 2 1568,
   opAt 2054 .MSTORE,
   opAt 2055 (.Dup ⟨1, by decide⟩),
   opAt 2056 (.Dup ⟨0, by decide⟩),
   pushAt 2057 0 0,
   opAt 2058 .SUB,
   opAt 2059 .DIV,
   pushAt 2060 1 1,
   opAt 2061 .ADD,
   pushAt 2062 2 1600,
   opAt 2063 .MSTORE,
   opAt 2064 (.Dup ⟨0, by decide⟩),
   opAt 2065 (.Dup ⟨0, by decide⟩),
   pushAt 2066 0 0,
   opAt 2067 .SUB,
   opAt 2068 .MOD,
   pushAt 2069 2 1632,
   opAt 2070 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2071 (.Dup ⟨0, by decide⟩),
   pushAt 2072 1 3,
   opAt 2073 .MUL,
   pushAt 2074 1 2,
   opAt 2075 .XOR,
   opAt 2076 (.Dup ⟨0, by decide⟩),
   opAt 2077 (.Dup ⟨2, by decide⟩),
   opAt 2078 .MUL,
   pushAt 2079 1 2,
   opAt 2080 .SUB,
   opAt 2081 .MUL,
   opAt 2082 (.Dup ⟨0, by decide⟩),
   opAt 2083 (.Dup ⟨2, by decide⟩),
   opAt 2084 .MUL,
   pushAt 2085 1 2,
   opAt 2086 .SUB,
   opAt 2087 .MUL,
   opAt 2088 (.Dup ⟨0, by decide⟩),
   opAt 2089 (.Dup ⟨2, by decide⟩),
   opAt 2090 .MUL,
   pushAt 2091 1 2,
   opAt 2092 .SUB,
   opAt 2093 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2094 (.Dup ⟨0, by decide⟩),
   opAt 2095 (.Dup ⟨2, by decide⟩),
   opAt 2096 .MUL,
   pushAt 2097 1 2,
   opAt 2098 .SUB,
   opAt 2099 .MUL,
   opAt 2100 (.Dup ⟨0, by decide⟩),
   opAt 2101 (.Dup ⟨2, by decide⟩),
   opAt 2102 .MUL,
   pushAt 2103 1 2,
   opAt 2104 .SUB,
   opAt 2105 .MUL,
   opAt 2106 (.Dup ⟨0, by decide⟩),
   opAt 2107 (.Dup ⟨2, by decide⟩),
   opAt 2108 .MUL,
   pushAt 2109 1 2,
   opAt 2110 .SUB,
   opAt 2111 .MUL,
   pushAt 2112 2 1664,
   opAt 2113 .MSTORE,
   opAt 2114 .POP,
   opAt 2115 .POP,
   opAt 2116 .POP,
   pushAt 2117 0 0,
   pushAt 2118 0 0,
   opAt 2119 (.Dup ⟨4, by decide⟩),
   opAt 2120 (.Dup ⟨4, by decide⟩),
   opAt 2121 (.Dup ⟨7, by decide⟩),
   pushAt 2122 2 1536,
   opAt 2123 .MLOAD,
   pushAt 2124 2 1568,
   opAt 2125 .MLOAD,
   pushAt 2126 2 1664,
   opAt 2127 .MLOAD,
   pushAt 2128 2 1632,
   opAt 2129 .MLOAD,
   pushAt 2130 2 1504,
   opAt 2131 .MLOAD,
   pushAt 2132 2 1472,
   opAt 2133 .MLOAD,
   pushAt 2134 2 1440,
   opAt 2135 .MLOAD,
   pushAt 2136 2 1408,
   opAt 2137 .MLOAD,
   pushAt 2138 2 1376,
   opAt 2139 .MLOAD,
   pushAt 2140 2 1344,
   opAt 2141 .MLOAD,
   pushAt 2142 2 1312,
   opAt 2143 .MLOAD,
   opAt 2144 (.Dup ⟨12, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2177 .JUMPDEST,
   opAt 2178 (.Dup ⟨0, by decide⟩),
   opAt 2179 .ISZERO,
   pushAt 2180 2 3346,
   opAt 2181 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2182 (.Dup ⟨15, by decide⟩),
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
   opAt 2192 (.Dup ⟨13, by decide⟩),
   opAt 2193 (.Dup ⟨1, by decide⟩),
   opAt 2194 .DIV,
   opAt 2195 (.Swap ⟨0, by decide⟩),
   pushAt 2196 2 1600,
   opAt 2197 .MLOAD,
   opAt 2198 .MUL,
   opAt 2199 (.Dup ⟨14, by decide⟩),
   pushAt 2200 2 2112,
   opAt 2201 .MLOAD,
   opAt 2202 .DIV,
   opAt 2203 .ADD,
   opAt 2204 (.Dup ⟨13, by decide⟩),
   opAt 2205 (.Dup ⟨0, by decide⟩),
   opAt 2206 (.Dup ⟨13, by decide⟩),
   opAt 2207 (.Dup ⟨4, by decide⟩),
   opAt 2208 .MULMOD,
   opAt 2209 (.Dup ⟨2, by decide⟩),
   opAt 2210 .ADDMOD,
   opAt 2211 (.Swap ⟨0, by decide⟩),
   opAt 2212 .SUB,
   opAt 2213 (.Dup ⟨12, by decide⟩),
   opAt 2214 .MUL,
   opAt 2215 (.Dup ⟨0, by decide⟩),
   pushAt 2216 0 0,
   opAt 2217 .MLOAD,
   opAt 2218 .MUL,
   pushAt 2219 2 2112,
   opAt 2220 .MLOAD,
   opAt 2221 .SUB,
   pushAt 2222 1 32,
   opAt 2223 .MLOAD,
   pushAt 2224 1 128,
   opAt 2225 .SHR,
   opAt 2226 (.Dup ⟨2, by decide⟩),
   pushAt 2227 1 128,
   opAt 2228 .SHR,
   opAt 2229 .MUL,
   opAt 2230 .GT,
   opAt 2231 (.Swap ⟨0, by decide⟩),
   opAt 2232 .SUB,
   pushAt 2233 0 0,
   opAt 2234 .NOT,
   opAt 2235 (.Swap ⟨1, by decide⟩),
   opAt 2236 (.Dup ⟨14, by decide⟩),
   opAt 2237 .GT,
   opAt 2238 .ISZERO,
   pushAt 2239 0 0,
   opAt 2240 .SUB,
   opAt 2241 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2462 2 2080,
   opAt 2463 .MLOAD,
   opAt 2464 (.Dup ⟨1, by decide⟩),
   opAt 2465 .ADD,
   opAt 2466 (.Dup ⟨0, by decide⟩),
   opAt 2467 (.Swap ⟨1, by decide⟩),
   opAt 2468 .GT,
   opAt 2469 (.Dup ⟨1, by decide⟩),
   opAt 2470 (.Dup ⟨3, by decide⟩),
   opAt 2471 .GT,
   opAt 2472 .GT,
   opAt 2473 (.Swap ⟨2, by decide⟩),
   opAt 2474 .POP,
   opAt 2475 .SUB,
   opAt 2476 (.Dup ⟨0, by decide⟩),
   pushAt 2477 2 2080,
   opAt 2478 .MSTORE,
   opAt 2479 (.Dup ⟨1, by decide⟩),
   opAt 2480 .OR,
   pushAt 2481 2 3208,
   opAt 2482 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2494 .JUMPDEST,
   opAt 2495 .ISZERO,
   pushAt 2496 2 3287,
   opAt 2497 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2498 .JUMPDEST,
   pushAt 2499 0 0,
   pushAt 2500 2 2784,
   opAt 2501 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2502 .JUMPDEST,
   opAt 2503 (.Dup ⟨0, by decide⟩),
   opAt 2504 .MLOAD,
   pushAt 2505 2 2112,
   opAt 2506 (.Dup ⟨2, by decide⟩),
   opAt 2507 .SUB,
   opAt 2508 .MLOAD,
   opAt 2509 (.Dup ⟨1, by decide⟩),
   opAt 2510 .ADD,
   opAt 2511 (.Swap ⟨0, by decide⟩),
   opAt 2512 (.Dup ⟨1, by decide⟩),
   opAt 2513 .LT,
   opAt 2514 (.Swap ⟨0, by decide⟩),
   opAt 2515 (.Dup ⟨3, by decide⟩),
   opAt 2516 .ADD,
   opAt 2517 (.Swap ⟨2, by decide⟩),
   opAt 2518 (.Dup ⟨3, by decide⟩),
   opAt 2519 .LT,
   opAt 2520 .OR,
   opAt 2521 (.Swap ⟨1, by decide⟩),
   opAt 2522 (.Dup ⟨1, by decide⟩),
   opAt 2523 .MSTORE,
   pushAt 2524 1 31,
   opAt 2525 .NOT,
   opAt 2526 .ADD,
   pushAt 2527 2 2111,
   opAt 2528 (.Dup ⟨1, by decide⟩),
   opAt 2529 .GT,
   pushAt 2530 2 3220,
   opAt 2531 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2532 .POP,
   pushAt 2533 2 2080,
   opAt 2534 .MLOAD,
   opAt 2535 (.Dup ⟨1, by decide⟩),
   opAt 2536 .ADD,
   opAt 2537 (.Dup ⟨0, by decide⟩),
   pushAt 2538 2 2080,
   opAt 2539 .MSTORE,
   opAt 2540 .LT,
   opAt 2541 .ISZERO,
   pushAt 2542 2 3214,
   opAt 2543 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2544 .JUMPDEST,
   pushAt 2545 2 2080,
   opAt 2546 .MLOAD,
   opAt 2547 (.Dup ⟨0, by decide⟩),
   opAt 2548 .ISZERO,
   pushAt 2549 2 3195,
   opAt 2550 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2544 .JUMPDEST,
   pushAt 2545 2 2080,
   opAt 2546 .MLOAD,
   opAt 2547 (.Dup ⟨0, by decide⟩),
   opAt 2548 .ISZERO,
   pushAt 2549 2 3195,
   opAt 2550 .JUMPI,
   opAt 2551 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2552 .JUMPDEST,
   pushAt 2553 0 0,
   pushAt 2554 2 2784,
   opAt 2555 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2556 .JUMPDEST,
   opAt 2557 (.Dup ⟨0, by decide⟩),
   opAt 2558 .MLOAD,
   pushAt 2559 2 2112,
   opAt 2560 (.Dup ⟨2, by decide⟩),
   opAt 2561 .SUB,
   opAt 2562 .MLOAD,
   opAt 2563 (.Dup ⟨1, by decide⟩),
   opAt 2564 (.Dup ⟨1, by decide⟩),
   opAt 2565 .GT,
   opAt 2566 (.Swap ⟨1, by decide⟩),
   opAt 2567 .SUB,
   opAt 2568 (.Dup ⟨3, by decide⟩),
   opAt 2569 (.Dup ⟨1, by decide⟩),
   opAt 2570 .LT,
   opAt 2571 (.Swap ⟨0, by decide⟩),
   opAt 2572 (.Dup ⟨4, by decide⟩),
   opAt 2573 (.Swap ⟨0, by decide⟩),
   opAt 2574 .SUB,
   opAt 2575 (.Dup ⟨3, by decide⟩),
   opAt 2576 .MSTORE,
   opAt 2577 .OR,
   opAt 2578 (.Swap ⟨1, by decide⟩),
   opAt 2579 .POP,
   pushAt 2580 1 31,
   opAt 2581 .NOT,
   opAt 2582 .ADD,
   pushAt 2583 2 2111,
   opAt 2584 (.Dup ⟨1, by decide⟩),
   opAt 2585 .GT,
   pushAt 2586 2 3284,
   opAt 2587 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2588 .POP,
   pushAt 2589 2 2080,
   opAt 2590 .MLOAD,
   opAt 2591 .SUB,
   pushAt 2592 2 2080,
   opAt 2593 .MSTORE,
   pushAt 2594 2 3266,
   opAt 2595 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), jump straight to the loop head (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2483 .JUMPDEST,
   opAt 2484 .NOT,
   opAt 2485 .ADD,
   pushAt 2486 2 2811,
   opAt 2487 .JUMP]

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
  Artifact.isValidJumpDest_index 2177 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3214 = true :=
  Artifact.isValidJumpDest_index 2498 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3220 = true :=
  Artifact.isValidJumpDest_index 2502 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3275 = true :=
  Artifact.isValidJumpDest_index 2544 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3293 = true :=
  Artifact.isValidJumpDest_index 2556 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3208 = true :=
  Artifact.isValidJumpDest_index 2494 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3287 = true :=
  Artifact.isValidJumpDest_index 2552 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3195 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3346 = true :=
  Artifact.isValidJumpDest_index 2596 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5444 = true :=
  Artifact.isValidJumpDest_index 4280 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2471 = true :=
  Artifact.isValidJumpDest_index 1952 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2899 + 133·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2145 (.Dup ⟨0, by decide⟩),
   pushAt 2146 1 4,
   opAt 2147 .EQ,
   pushAt 2148 1 133,
   opAt 2149 .MUL,
   pushAt 2150 2 2899,
   opAt 2151 .ADD,
   pushAt 2152 2 1698,
   opAt 2153 .MSTORE,
   opAt 2154 (.Dup ⟨12, by decide⟩),
   pushAt 2155 1 1,
   opAt 2156 .EQ,
   pushAt 2157 2 2816,
   opAt 2158 .MLOAD,
   opAt 2159 .CALLDATALOAD,
   pushAt 2160 0 0,
   opAt 2161 .BYTE,
   pushAt 2162 1 3,
   opAt 2163 .EQ,
   opAt 2164 .AND,
   opAt 2165 (.Dup ⟨1, by decide⟩),
   pushAt 2166 1 3,
   opAt 2167 .AND,
   opAt 2168 .ISZERO,
   opAt 2169 .AND,
   opAt 2170 (.Dup ⟨0, by decide⟩),
   pushAt 2171 2 1760,
   opAt 2172 .MSTORE,
   opAt 2173 .SHR,
   pushAt 2174 2 1698,
   opAt 2175 .MLOAD,
   opAt 2176 (.Swap ⟨0, by decide⟩)]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3380). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2596 .JUMPDEST,
   opAt 2597 .POP,
   pushAt 2598 2 1760,
   opAt 2599 .MLOAD,
   opAt 2600 .ISZERO,
   pushAt 2601 2 5444,
   opAt 2602 .JUMPI]

/-- The cleanup tail (pcs 5444-5465): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `30` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4280 .JUMPDEST,
   opAt 4281 .POP,
   opAt 4282 .POP,
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
   pushAt 4297 2 2441,
   opAt 4298 .ADD,
   opAt 4299 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
