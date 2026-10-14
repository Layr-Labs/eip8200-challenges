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
  [opAt 1938 .JUMPDEST,
   opAt 1939 (.Dup ⟨0, by decide⟩),
   opAt 1940 (.Dup ⟨3, by decide⟩),
   opAt 1941 .EQ,
   pushAt 1942 0 0,
   opAt 1943 .MLOAD,
   pushAt 1944 1 255,
   opAt 1945 .SHR,
   opAt 1946 .AND,
   opAt 1947 .ISZERO,
   pushAt 1948 2 761,
   opAt 1949 .JUMPI]

/-- `BAIL6` (pc 1054): the six-word bail trampoline the full-base miss now names.
It lands on `modexpBig` at pc 237 with the outer frame untouched. -/
def bailBlock :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 545 .JUMPDEST,
   pushAt 546 1 218,
   opAt 547 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1950 (.Dup ⟨0, by decide⟩),
   pushAt 1951 1 96,
   pushAt 1952 2 2112,
   opAt 1953 .CALLDATACOPY,
   pushAt 1954 2 2494,
   pushAt 1955 2 4033,
   opAt 1956 .JUMP]


/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1962 2 2752,
   opAt 1963 .MLOAD,
   pushAt 1964 1 1]

/-- `blk2919`, first part (pc 2658..2671): the four pads, drop the loop words, and
`L = d &&& -d` twice on top of `d`.  The block stops before the `CLZ` at pc 2672, which the
shared stepper cannot run (`ClzStep.gasSteps_clz`). -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1982 .JUMPDEST,
   opAt 1983 .JUMPDEST,
   opAt 1984 .JUMPDEST,
   opAt 1985 .JUMPDEST,
   opAt 1986 .POP,
   opAt 1987 .POP,
   pushAt 1988 0 0,
   opAt 1989 .MLOAD,
   opAt 1990 (.Dup ⟨0, by decide⟩),
   pushAt 1991 0 0,
   opAt 1992 .SUB,
   opAt 1993 (.Dup ⟨1, by decide⟩),
   opAt 1994 .AND,
   opAt 1995 (.Dup ⟨0, by decide⟩)]

/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1997 (.Dup ⟨0, by decide⟩),
   opAt 1998 .NOT,
   pushAt 1999 0 0,
   opAt 2000 .SUB,
   pushAt 2001 2 1600,
   opAt 2002 .MSTORE,
   pushAt 2003 1 255,
   opAt 2004 .SUB,
   pushAt 2005 2 1536,
   opAt 2006 .MSTORE,
   opAt 2007 (.Dup ⟨0, by decide⟩),
   opAt 2008 (.Dup ⟨2, by decide⟩),
   opAt 2009 .DIV,
   opAt 2010 (.Dup ⟨0, by decide⟩),
   pushAt 2011 2 1568,
   opAt 2012 .MSTORE,
   opAt 2013 (.Dup ⟨0, by decide⟩),
   opAt 2014 (.Dup ⟨0, by decide⟩),
   pushAt 2015 0 0,
   opAt 2016 .SUB,
   opAt 2017 .MOD,
   pushAt 2018 2 1632,
   opAt 2019 .MSTORE]

/-- newton-batch head (pc 2705): load the modulus low limb `n0 = mem[mem[0xac0]]`, call the
shared Newton chain on `dodd * n0` with return pc 2741. -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2020 2 2752,
   opAt 2021 .MLOAD,
   opAt 2022 .MLOAD,
   pushAt 2023 2 2593,
   opAt 2024 (.Dup ⟨1, by decide⟩),
   opAt 2025 (.Dup ⟨3, by decide⟩),
   opAt 2026 .MUL,
   pushAt 2027 2 693,
   opAt 2028 .JUMP]

/-- The shared Newton chain (pc 714): `[p, ret]` becomes `[newton8W p]` at `ret`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 489 .JUMPDEST,
   opAt 490 (.Dup ⟨0, by decide⟩),
   pushAt 491 1 3,
   opAt 492 .MUL,
   pushAt 493 1 2,
   opAt 494 .XOR,
   opAt 495 (.Dup ⟨0, by decide⟩),
   opAt 496 (.Dup ⟨2, by decide⟩),
   opAt 497 .MUL,
   pushAt 498 1 2,
   opAt 499 .SUB,
   opAt 500 .MUL,
   opAt 501 (.Dup ⟨0, by decide⟩),
   opAt 502 (.Dup ⟨2, by decide⟩),
   opAt 503 .MUL,
   pushAt 504 1 2,
   opAt 505 .SUB,
   opAt 506 .MUL,
   opAt 507 (.Dup ⟨0, by decide⟩),
   opAt 508 (.Dup ⟨2, by decide⟩),
   opAt 509 .MUL,
   pushAt 510 1 2,
   opAt 511 .SUB,
   opAt 512 .MUL,
   opAt 513 (.Dup ⟨0, by decide⟩),
   opAt 514 (.Dup ⟨2, by decide⟩),
   opAt 515 .MUL,
   pushAt 516 1 2,
   opAt 517 .SUB,
   opAt 518 .MUL,
   opAt 519 (.Dup ⟨0, by decide⟩),
   opAt 520 (.Dup ⟨2, by decide⟩),
   opAt 521 .MUL,
   pushAt 522 1 2,
   opAt 523 .SUB,
   opAt 524 .MUL,
   opAt 525 (.Dup ⟨0, by decide⟩),
   opAt 526 (.Dup ⟨2, by decide⟩),
   opAt 527 .MUL,
   pushAt 528 1 2,
   opAt 529 .SUB,
   opAt 530 .MUL,
   opAt 531 (.Swap ⟨1, by decide⟩),
   opAt 532 (.Swap ⟨0, by decide⟩),
   opAt 533 .POP,
   opAt 534 .JUMP]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2029 .JUMPDEST,
   opAt 2030 (.Dup ⟨1, by decide⟩),
   opAt 2031 (.Dup ⟨1, by decide⟩),
   opAt 2032 .MUL,
   pushAt 2033 2 1664,
   opAt 2034 .MSTORE,
   opAt 2035 (.Dup ⟨2, by decide⟩),
   opAt 2036 .MUL,
   pushAt 2037 0 0,
   opAt 2038 .SUB,
   pushAt 2039 2 2720,
   opAt 2040 .MSTORE,
   opAt 2041 .POP,
   opAt 2042 .POP,
   opAt 2043 .POP,
   opAt 2044 .POP,
   pushAt 2045 0 0,
   pushAt 2046 0 0,
   opAt 2047 (.Dup ⟨4, by decide⟩),
   opAt 2048 (.Dup ⟨4, by decide⟩),
   opAt 2049 (.Dup ⟨7, by decide⟩),
   pushAt 2050 2 1536,
   opAt 2051 .MLOAD,
   pushAt 2052 2 1568,
   opAt 2053 .MLOAD,
   pushAt 2054 2 1664,
   opAt 2055 .MLOAD,
   pushAt 2056 2 1632,
   opAt 2057 .MLOAD,
   pushAt 2058 2 1504,
   opAt 2059 .MLOAD,
   pushAt 2060 2 1472,
   opAt 2061 .MLOAD,
   pushAt 2062 2 1440,
   opAt 2063 .MLOAD,
   pushAt 2064 2 1408,
   opAt 2065 .MLOAD,
   pushAt 2066 2 1376,
   opAt 2067 .MLOAD,
   pushAt 2068 2 1344,
   opAt 2069 .MLOAD,
   pushAt 2070 2 1312,
   opAt 2071 .MLOAD,
   opAt 2072 (.Dup ⟨12, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2105 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2106 (.Dup ⟨15, by decide⟩),
   pushAt 2107 2 2112,
   pushAt 2108 2 2080,
   opAt 2109 .MCOPY,
   pushAt 2110 0 0,
   pushAt 2111 2 2784,
   opAt 2112 .MLOAD,
   opAt 2113 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2114 2 2080,
   opAt 2115 .MLOAD,
   opAt 2116 (.Dup ⟨0, by decide⟩),
   opAt 2117 (.Dup ⟨14, by decide⟩),
   opAt 2118 .SHR,
   opAt 2119 (.Swap ⟨0, by decide⟩),
   pushAt 2120 2 1600,
   opAt 2121 .MLOAD,
   opAt 2122 .SHL,
   pushAt 2123 2 2112,
   opAt 2124 .MLOAD,
   opAt 2125 (.Dup ⟨15, by decide⟩),
   opAt 2126 .SHR,
   opAt 2127 .ADD,
   opAt 2128 (.Dup ⟨13, by decide⟩),
   opAt 2129 (.Dup ⟨0, by decide⟩),
   opAt 2130 (.Dup ⟨13, by decide⟩),
   opAt 2131 (.Dup ⟨4, by decide⟩),
   opAt 2132 .MULMOD,
   opAt 2133 (.Dup ⟨2, by decide⟩),
   opAt 2134 .ADDMOD,
   opAt 2135 (.Swap ⟨0, by decide⟩),
   opAt 2136 .SUB,
   opAt 2137 (.Dup ⟨12, by decide⟩),
   opAt 2138 .MUL,
   opAt 2139 (.Dup ⟨0, by decide⟩),
   pushAt 2140 0 0,
   opAt 2141 .MLOAD,
   opAt 2142 .MUL,
   pushAt 2143 2 2112,
   opAt 2144 .MLOAD,
   opAt 2145 .SUB,
   pushAt 2146 1 32,
   opAt 2147 .MLOAD,
   pushAt 2148 1 128,
   opAt 2149 .SHR,
   opAt 2150 (.Dup ⟨2, by decide⟩),
   pushAt 2151 1 128,
   opAt 2152 .SHR,
   opAt 2153 .MUL,
   opAt 2154 .GT,
   opAt 2155 (.Swap ⟨0, by decide⟩),
   opAt 2156 .SUB,
   pushAt 2157 0 0,
   opAt 2158 .NOT,
   opAt 2159 (.Swap ⟨1, by decide⟩),
   opAt 2160 (.Dup ⟨14, by decide⟩),
   opAt 2161 .GT,
   opAt 2162 .ISZERO,
   pushAt 2163 0 0,
   opAt 2164 .SUB,
   opAt 2165 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2387 2 2080,
   opAt 2388 .MLOAD,
   opAt 2389 (.Dup ⟨1, by decide⟩),
   opAt 2390 .ADD,
   opAt 2391 (.Dup ⟨0, by decide⟩),
   opAt 2392 (.Swap ⟨1, by decide⟩),
   opAt 2393 .GT,
   opAt 2394 (.Dup ⟨1, by decide⟩),
   opAt 2395 (.Dup ⟨3, by decide⟩),
   opAt 2396 .GT,
   opAt 2397 .GT,
   opAt 2398 (.Swap ⟨2, by decide⟩),
   opAt 2399 .POP,
   opAt 2400 .SUB,
   opAt 2401 (.Dup ⟨0, by decide⟩),
   pushAt 2402 2 2080,
   opAt 2403 .MSTORE,
   opAt 2404 (.Dup ⟨1, by decide⟩),
   opAt 2405 .OR,
   pushAt 2406 2 3080,
   opAt 2407 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2416 .JUMPDEST,
   opAt 2417 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2418 .JUMPDEST,
   pushAt 2419 0 0,
   pushAt 2420 2 2784,
   opAt 2421 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2422 .JUMPDEST,
   opAt 2423 (.Dup ⟨0, by decide⟩),
   opAt 2424 .MLOAD,
   pushAt 2425 2 2112,
   opAt 2426 (.Dup ⟨2, by decide⟩),
   opAt 2427 .SUB,
   opAt 2428 .MLOAD,
   opAt 2429 (.Dup ⟨1, by decide⟩),
   opAt 2430 .ADD,
   opAt 2431 (.Swap ⟨0, by decide⟩),
   opAt 2432 (.Dup ⟨1, by decide⟩),
   opAt 2433 .LT,
   opAt 2434 (.Swap ⟨0, by decide⟩),
   opAt 2435 (.Dup ⟨3, by decide⟩),
   opAt 2436 .ADD,
   opAt 2437 (.Swap ⟨2, by decide⟩),
   opAt 2438 (.Dup ⟨3, by decide⟩),
   opAt 2439 .LT,
   opAt 2440 .OR,
   opAt 2441 (.Swap ⟨1, by decide⟩),
   opAt 2442 (.Dup ⟨1, by decide⟩),
   opAt 2443 .MSTORE,
   pushAt 2444 1 31,
   opAt 2445 .NOT,
   opAt 2446 .ADD,
   pushAt 2447 2 2111,
   opAt 2448 (.Dup ⟨1, by decide⟩),
   opAt 2449 .GT,
   pushAt 2450 2 3088,
   opAt 2451 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2452 .POP,
   pushAt 2453 2 2080,
   opAt 2454 .MLOAD,
   opAt 2455 (.Dup ⟨1, by decide⟩),
   opAt 2456 .ADD,
   opAt 2457 (.Dup ⟨0, by decide⟩),
   pushAt 2458 2 2080,
   opAt 2459 .MSTORE,
   opAt 2460 .LT,
   opAt 2461 .ISZERO,
   pushAt 2462 2 3082,
   opAt 2463 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2464 .JUMPDEST,
   pushAt 2465 2 2080,
   opAt 2466 .MLOAD,
   opAt 2467 (.Dup ⟨0, by decide⟩),
   opAt 2468 .ISZERO,
   pushAt 2469 2 3068,
   opAt 2470 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2408 .JUMPDEST,
   opAt 2409 .NOT,
   opAt 2410 .ADD,
   opAt 2411 (.Dup ⟨0, by decide⟩),
   pushAt 2412 2 2710,
   opAt 2413 .JUMPI]

/-- The loop exit after the last step: jump to `SHIFT_DONE`. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2414 2 3154,
   opAt 2415 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2465 = true :=
  Artifact.isValidJumpDest_index 1938 (by rfl)

/-- `BAIL6`, the target of the full-base miss. -/
theorem jumpDest714 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 693 = true :=
  Artifact.isValidJumpDest_index 489 (by rfl)

theorem jumpDest2694 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2593 = true :=
  Artifact.isValidJumpDest_index 2029 (by rfl)

theorem jumpDestBail6 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 761 = true :=
  Artifact.isValidJumpDest_index 545 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 218 = true :=
  Artifact.isValidJumpDest_index 148 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2494 = true :=
  Artifact.isValidJumpDest_index 1957 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2509 = true :=
  Artifact.isValidJumpDest_index 1965 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2710 = true :=
  Artifact.isValidJumpDest_index 2105 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3082 = true :=
  Artifact.isValidJumpDest_index 2418 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3088 = true :=
  Artifact.isValidJumpDest_index 2422 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3143 = true :=
  Artifact.isValidJumpDest_index 2464 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3080 = true :=
  Artifact.isValidJumpDest_index 2416 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3068 = true :=
  Artifact.isValidJumpDest_index 2408 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3154 = true :=
  Artifact.isValidJumpDest_index 2471 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5546 = true :=
  Artifact.isValidJumpDest_index 4436 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2417 = true :=
  Artifact.isValidJumpDest_index 1912 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2946 + 116·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2073 (.Dup ⟨0, by decide⟩),
   pushAt 2074 1 4,
   opAt 2075 .EQ,
   pushAt 2076 1 116,
   opAt 2077 .MUL,
   pushAt 2078 2 2792,
   opAt 2079 .ADD,
   pushAt 2080 2 1698,
   opAt 2081 .MSTORE,
   opAt 2082 (.Dup ⟨12, by decide⟩),
   pushAt 2083 1 1,
   opAt 2084 .EQ,
   pushAt 2085 2 2816,
   opAt 2086 .MLOAD,
   opAt 2087 .CALLDATALOAD,
   pushAt 2088 0 0,
   opAt 2089 .BYTE,
   pushAt 2090 1 3,
   opAt 2091 .EQ,
   opAt 2092 .AND,
   opAt 2093 (.Dup ⟨1, by decide⟩),
   pushAt 2094 1 3,
   opAt 2095 .AND,
   opAt 2096 .ISZERO,
   opAt 2097 .AND,
   opAt 2098 (.Dup ⟨0, by decide⟩),
   pushAt 2099 2 1760,
   opAt 2100 .MSTORE,
   opAt 2101 .SHR,
   pushAt 2102 2 1698,
   opAt 2103 .MLOAD,
   opAt 2104 (.Swap ⟨0, by decide⟩)]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3380). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2471 .JUMPDEST,
   opAt 2472 .POP,
   pushAt 2473 2 1760,
   opAt 2474 .MLOAD,
   opAt 2475 .ISZERO,
   pushAt 2476 2 5546,
   opAt 2477 .JUMPI]

/-- The cleanup tail (pcs 5444-5465): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4436 .JUMPDEST,
   opAt 4437 .POP,
   opAt 4438 .POP,
   opAt 4439 .POP,
   opAt 4440 .POP,
   opAt 4441 .POP,
   opAt 4442 .POP,
   opAt 4443 .POP,
   opAt 4444 .POP,
   opAt 4445 .POP,
   opAt 4446 .POP,
   opAt 4447 .POP,
   opAt 4448 .POP,
   opAt 4449 .POP,
   opAt 4450 .POP,
   opAt 4451 .POP,
   opAt 4452 .POP,
   pushAt 4453 2 2389,
   opAt 4454 .ADD,
   opAt 4455 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
