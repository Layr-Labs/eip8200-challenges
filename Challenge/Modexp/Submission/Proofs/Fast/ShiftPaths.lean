import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The dispatcher guard (k2465): `bsize = 32 n` or jump straight to `modexpBig` (pc 219). -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1878 .JUMPDEST,
   opAt 1879 (.Dup ⟨0, by decide⟩),
   opAt 1880 (.Dup ⟨3, by decide⟩),
   opAt 1881 .EQ,
   opAt 1882 .ISZERO,
   pushAt 1883 1 219,
   opAt 1884 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1885 (.Dup ⟨0, by decide⟩),
   pushAt 1886 1 96,
   pushAt 1887 2 2112,
   opAt 1888 .CALLDATACOPY,
   pushAt 1889 2 2412,
   pushAt 1890 2 4010,
   opAt 1891 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1897 (.Dup ⟨0, by decide⟩),
   pushAt 1898 1 128,
   opAt 1899 .EQ,
   pushAt 1900 2 2336,
   opAt 1901 .JUMPI]

/-- Negation cell at pc 2429: `NEG[1504] := 0 - mem[224]`. -/
def negS8 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1902 1 224,
   opAt 1903 .MLOAD,
   pushAt 1904 0 0,
   opAt 1905 .SUB,
   pushAt 1906 2 1504,
   opAt 1907 .MSTORE]

/-- Negation cell at pc 2438: `NEG[1472] := NOT mem[192]`. -/
def negN8a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1908 1 192,
   opAt 1909 .MLOAD,
   opAt 1910 .NOT,
   pushAt 1911 2 1472,
   opAt 1912 .MSTORE]

/-- Negation cell at pc 2446: `NEG[1440] := NOT mem[160]`. -/
def negN8b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1913 1 160,
   opAt 1914 .MLOAD,
   opAt 1915 .NOT,
   pushAt 1916 2 1440,
   opAt 1917 .MSTORE]

/-- Negation cell at pc 2454: `NEG[1408] := NOT mem[128]`. -/
def negN8c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1918 1 128,
   opAt 1919 .MLOAD,
   opAt 1920 .NOT,
   pushAt 1921 2 1408,
   opAt 1922 .MSTORE]

/-- Negation cell at pc 2462: `NEG[1376] := NOT mem[96]`. -/
def negN8d :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1923 1 96,
   opAt 1924 .MLOAD,
   opAt 1925 .NOT,
   pushAt 1926 2 1376,
   opAt 1927 .MSTORE]

/-- Negation cell at pc 2471: `NEG[1344] := NOT mem[64]`. -/
def negNTa :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1929 1 64,
   opAt 1930 .MLOAD,
   opAt 1931 .NOT,
   pushAt 1932 2 1344,
   opAt 1933 .MSTORE]

/-- Negation cell at pc 2479: `NEG[1312] := NOT mem[32]`. -/
def negNTb :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1934 1 32,
   opAt 1935 .MLOAD,
   opAt 1936 .NOT,
   pushAt 1937 2 1312,
   opAt 1938 .MSTORE]

/-- Negation cell at pc 2487: `NEG[1280] := NOT mem[0]`. -/
def negNTc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1939 0 0,
   opAt 1940 .MLOAD,
   opAt 1941 .NOT,
   pushAt 1942 2 1280,
   opAt 1943 .MSTORE]

/-- Negation cell at pc 2337: `NEG[1376] := 0 - mem[96]`. -/
def negS4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1848 1 96,
   opAt 1849 .MLOAD,
   pushAt 1850 0 0,
   opAt 1851 .SUB,
   pushAt 1852 2 1376,
   opAt 1853 .MSTORE]

/-- The four-limb stub's `JUMPDEST` (pc 2336). -/
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1847 .JUMPDEST]

/-- The four-limb stub joins `NEG_TAIL` (pc 2470). -/
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1854 2 2470,
   opAt 1855 .JUMP]

/-- `NEG_TAIL`'s `JUMPDEST` (pc 2470). -/
def negJT :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1928 .JUMPDEST]

/-- Eight-limb negation cells 7..3 (limb 7: `0 - m_7`), falling into `NEG_TAIL`. -/
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

/-- Four-limb negation stub (pc 2336): limb 3 as `0 - m_3`, then `NEG_TAIL` at pc 2470. -/
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

/-- `NEG_TAIL` (pc 2470): negation cells 2..0. -/
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  negJT ++ negNTa ++ negNTb ++ negNTc

/-- `blk2919`, first part: `L = d &&& -d` twice on top of `d`, stopping before the `CLZ`. -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1944 0 0,
   opAt 1945 .MLOAD,
   opAt 1946 (.Dup ⟨0, by decide⟩),
   pushAt 1947 0 0,
   opAt 1948 .SUB,
   opAt 1949 (.Dup ⟨1, by decide⟩),
   opAt 1950 .AND,
   opAt 1951 (.Dup ⟨0, by decide⟩)]

/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1953 (.Dup ⟨0, by decide⟩),
   opAt 1954 .NOT,
   pushAt 1955 0 0,
   opAt 1956 .SUB,
   pushAt 1957 2 1600,
   opAt 1958 .MSTORE,
   pushAt 1959 1 255,
   opAt 1960 .SUB,
   pushAt 1961 2 1536,
   opAt 1962 .MSTORE,
   opAt 1963 (.Dup ⟨0, by decide⟩),
   opAt 1964 (.Dup ⟨2, by decide⟩),
   opAt 1965 .DIV,
   opAt 1966 (.Dup ⟨0, by decide⟩),
   pushAt 1967 2 1568,
   opAt 1968 .MSTORE,
   opAt 1969 (.Dup ⟨0, by decide⟩),
   opAt 1970 (.Dup ⟨0, by decide⟩),
   pushAt 1971 0 0,
   opAt 1972 .SUB,
   opAt 1973 .MOD,
   pushAt 1974 2 1632,
   opAt 1975 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1976 2 2752,
   opAt 1977 .MLOAD,
   opAt 1978 .MLOAD,
   opAt 1979 (.Dup ⟨0, by decide⟩),
   opAt 1980 (.Dup ⟨2, by decide⟩),
   opAt 1981 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1982 (.Dup ⟨0, by decide⟩),
   pushAt 1983 1 3,
   opAt 1984 .MUL,
   pushAt 1985 1 2,
   opAt 1986 .XOR,
   opAt 1987 (.Dup ⟨0, by decide⟩),
   opAt 1988 (.Dup ⟨2, by decide⟩),
   opAt 1989 .MUL,
   pushAt 1990 1 2,
   opAt 1991 .SUB,
   opAt 1992 .MUL,
   opAt 1993 (.Dup ⟨0, by decide⟩),
   opAt 1994 (.Dup ⟨2, by decide⟩),
   opAt 1995 .MUL,
   pushAt 1996 1 2,
   opAt 1997 .SUB,
   opAt 1998 .MUL,
   opAt 1999 (.Dup ⟨0, by decide⟩),
   opAt 2000 (.Dup ⟨2, by decide⟩),
   opAt 2001 .MUL,
   pushAt 2002 1 2,
   opAt 2003 .SUB,
   opAt 2004 .MUL,
   opAt 2005 (.Dup ⟨0, by decide⟩),
   opAt 2006 (.Dup ⟨2, by decide⟩),
   opAt 2007 .MUL,
   pushAt 2008 1 2,
   opAt 2009 .SUB,
   opAt 2010 .MUL,
   opAt 2011 (.Dup ⟨0, by decide⟩),
   opAt 2012 (.Dup ⟨2, by decide⟩),
   opAt 2013 .MUL,
   pushAt 2014 1 2,
   opAt 2015 .SUB,
   opAt 2016 .MUL,
   opAt 2017 (.Dup ⟨0, by decide⟩),
   opAt 2018 (.Dup ⟨2, by decide⟩),
   opAt 2019 .MUL,
   pushAt 2020 1 2,
   opAt 2021 .SUB,
   opAt 2022 .MUL,
   opAt 2023 (.Swap ⟨0, by decide⟩),
   opAt 2024 .POP]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2025 (.Dup ⟨1, by decide⟩),
   opAt 2026 (.Dup ⟨1, by decide⟩),
   opAt 2027 .MUL,
   pushAt 2028 2 1664,
   opAt 2029 .MSTORE,
   opAt 2030 (.Dup ⟨2, by decide⟩),
   opAt 2031 .MUL,
   pushAt 2032 0 0,
   opAt 2033 .SUB,
   pushAt 2034 2 2720,
   opAt 2035 .MSTORE,
   opAt 2036 .POP,
   opAt 2037 .POP,
   opAt 2038 .POP,
   opAt 2039 .POP,
   pushAt 2040 0 0,
   pushAt 2041 0 0,
   opAt 2042 (.Dup ⟨4, by decide⟩),
   opAt 2043 (.Dup ⟨4, by decide⟩),
   opAt 2044 (.Dup ⟨7, by decide⟩),
   pushAt 2045 2 1536,
   opAt 2046 .MLOAD,
   pushAt 2047 2 1568,
   opAt 2048 .MLOAD,
   pushAt 2049 2 1664,
   opAt 2050 .MLOAD,
   pushAt 2051 2 1632,
   opAt 2052 .MLOAD,
   pushAt 2053 2 1504,
   opAt 2054 .MLOAD,
   pushAt 2055 2 1472,
   opAt 2056 .MLOAD,
   pushAt 2057 2 1440,
   opAt 2058 .MLOAD,
   pushAt 2059 2 1408,
   opAt 2060 .MLOAD,
   pushAt 2061 2 1376,
   opAt 2062 .MLOAD,
   pushAt 2063 2 1344,
   opAt 2064 .MLOAD,
   pushAt 2065 2 1312,
   opAt 2066 .MLOAD,
   opAt 2067 (.Dup ⟨12, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2095 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2096 (.Dup ⟨15, by decide⟩),
   pushAt 2097 2 2112,
   pushAt 2098 2 2080,
   opAt 2099 .MCOPY,
   pushAt 2100 0 0,
   pushAt 2101 2 2784,
   opAt 2102 .MLOAD,
   opAt 2103 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2104 2 2080,
   opAt 2105 .MLOAD,
   opAt 2106 (.Dup ⟨0, by decide⟩),
   opAt 2107 (.Dup ⟨14, by decide⟩),
   opAt 2108 .SHR,
   opAt 2109 (.Swap ⟨0, by decide⟩),
   pushAt 2110 2 1600,
   opAt 2111 .MLOAD,
   opAt 2112 .SHL,
   pushAt 2113 2 2112,
   opAt 2114 .MLOAD,
   opAt 2115 (.Dup ⟨15, by decide⟩),
   opAt 2116 .SHR,
   opAt 2117 .ADD,
   opAt 2118 (.Dup ⟨13, by decide⟩),
   opAt 2119 (.Dup ⟨0, by decide⟩),
   opAt 2120 (.Dup ⟨13, by decide⟩),
   opAt 2121 (.Dup ⟨4, by decide⟩),
   opAt 2122 .MULMOD,
   opAt 2123 (.Dup ⟨2, by decide⟩),
   opAt 2124 .ADDMOD,
   opAt 2125 (.Swap ⟨0, by decide⟩),
   opAt 2126 .SUB,
   opAt 2127 (.Dup ⟨12, by decide⟩),
   opAt 2128 .MUL,
   opAt 2129 (.Dup ⟨0, by decide⟩),
   pushAt 2130 0 0,
   opAt 2131 .MLOAD,
   opAt 2132 .MUL,
   pushAt 2133 2 2112,
   opAt 2134 .MLOAD,
   opAt 2135 .SUB,
   pushAt 2136 1 32,
   opAt 2137 .MLOAD,
   pushAt 2138 1 128,
   opAt 2139 .SHR,
   opAt 2140 (.Dup ⟨2, by decide⟩),
   pushAt 2141 1 128,
   opAt 2142 .SHR,
   opAt 2143 .MUL,
   opAt 2144 .GT,
   opAt 2145 (.Swap ⟨0, by decide⟩),
   opAt 2146 .SUB,
   pushAt 2147 0 0,
   opAt 2148 .NOT,
   opAt 2149 (.Swap ⟨1, by decide⟩),
   opAt 2150 (.Dup ⟨14, by decide⟩),
   opAt 2151 .GT,
   opAt 2152 .ISZERO,
   pushAt 2153 0 0,
   opAt 2154 .SUB,
   opAt 2155 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2376 2 2080,
   opAt 2377 .MLOAD,
   opAt 2378 (.Dup ⟨1, by decide⟩),
   opAt 2379 .ADD,
   opAt 2380 (.Dup ⟨0, by decide⟩),
   opAt 2381 (.Swap ⟨1, by decide⟩),
   opAt 2382 .GT,
   opAt 2383 (.Dup ⟨1, by decide⟩),
   opAt 2384 (.Dup ⟨3, by decide⟩),
   opAt 2385 .GT,
   opAt 2386 .GT,
   opAt 2387 (.Swap ⟨2, by decide⟩),
   opAt 2388 .POP,
   opAt 2389 .SUB,
   opAt 2390 (.Dup ⟨0, by decide⟩),
   pushAt 2391 2 2080,
   opAt 2392 .MSTORE,
   opAt 2393 (.Dup ⟨1, by decide⟩),
   opAt 2394 .OR,
   pushAt 2395 2 3073,
   opAt 2396 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2405 .JUMPDEST,
   opAt 2406 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2407 .JUMPDEST,
   pushAt 2408 0 0,
   pushAt 2409 2 2784,
   opAt 2410 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2411 .JUMPDEST,
   opAt 2412 (.Dup ⟨0, by decide⟩),
   opAt 2413 .MLOAD,
   pushAt 2414 2 2112,
   opAt 2415 (.Dup ⟨2, by decide⟩),
   opAt 2416 .SUB,
   opAt 2417 .MLOAD,
   opAt 2418 (.Dup ⟨1, by decide⟩),
   opAt 2419 .ADD,
   opAt 2420 (.Swap ⟨0, by decide⟩),
   opAt 2421 (.Dup ⟨1, by decide⟩),
   opAt 2422 .LT,
   opAt 2423 (.Swap ⟨0, by decide⟩),
   opAt 2424 (.Dup ⟨3, by decide⟩),
   opAt 2425 .ADD,
   opAt 2426 (.Swap ⟨2, by decide⟩),
   opAt 2427 (.Dup ⟨3, by decide⟩),
   opAt 2428 .LT,
   opAt 2429 .OR,
   opAt 2430 (.Swap ⟨1, by decide⟩),
   opAt 2431 (.Dup ⟨1, by decide⟩),
   opAt 2432 .MSTORE,
   pushAt 2433 1 31,
   opAt 2434 .NOT,
   opAt 2435 .ADD,
   pushAt 2436 2 2111,
   opAt 2437 (.Dup ⟨1, by decide⟩),
   opAt 2438 .GT,
   pushAt 2439 2 3081,
   opAt 2440 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2441 .POP,
   pushAt 2442 2 2080,
   opAt 2443 .MLOAD,
   opAt 2444 (.Dup ⟨1, by decide⟩),
   opAt 2445 .ADD,
   opAt 2446 (.Dup ⟨0, by decide⟩),
   pushAt 2447 2 2080,
   opAt 2448 .MSTORE,
   opAt 2449 .LT,
   opAt 2450 .ISZERO,
   pushAt 2451 2 3075,
   opAt 2452 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2453 2 2080,
   opAt 2454 .MLOAD,
   opAt 2455 (.Dup ⟨0, by decide⟩),
   opAt 2456 .ISZERO,
   pushAt 2457 2 3061,
   opAt 2458 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2397 .JUMPDEST,
   opAt 2398 .NOT,
   opAt 2399 .ADD,
   opAt 2400 (.Dup ⟨0, by decide⟩),
   pushAt 2401 2 2704,
   opAt 2402 .JUMPI]

/-- The loop exit after the last step: jump to `SHIFT_DONE`. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2403 2 3146,
   opAt 2404 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2390 = true :=
  Artifact.isValidJumpDest_index 1878 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 219 = true :=
  Artifact.isValidJumpDest_index 148 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2412 = true :=
  Artifact.isValidJumpDest_index 1892 (by rfl)


theorem jumpDestNeg4 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2336 = true :=
  Artifact.isValidJumpDest_index 1847 (by rfl)

theorem jumpDestNegT :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2470 = true :=
  Artifact.isValidJumpDest_index 1928 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2704 = true :=
  Artifact.isValidJumpDest_index 2095 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3075 = true :=
  Artifact.isValidJumpDest_index 2407 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3081 = true :=
  Artifact.isValidJumpDest_index 2411 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3073 = true :=
  Artifact.isValidJumpDest_index 2405 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3061 = true :=
  Artifact.isValidJumpDest_index 2397 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3146 = true :=
  Artifact.isValidJumpDest_index 2459 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5518 = true :=
  Artifact.isValidJumpDest_index 4409 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2329 = true :=
  Artifact.isValidJumpDest_index 1843 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2946 + 116·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2068 (.Dup ⟨0, by decide⟩),
   pushAt 2069 1 4,
   opAt 2070 .EQ,
   pushAt 2071 1 116,
   opAt 2072 .MUL,
   pushAt 2073 2 2785,
   opAt 2074 .ADD,
   pushAt 2075 2 1698,
   opAt 2076 .MSTORE,
   opAt 2077 (.Dup ⟨12, by decide⟩),
   pushAt 2078 1 1,
   opAt 2079 .EQ,
   pushAt 2080 2 2816,
   opAt 2081 .MLOAD,
   opAt 2082 .CALLDATALOAD,
   pushAt 2083 0 0,
   opAt 2084 .BYTE,
   pushAt 2085 1 3,
   opAt 2086 .EQ,
   opAt 2087 .AND,
   opAt 2088 (.Dup ⟨0, by decide⟩),
   pushAt 2089 2 1760,
   opAt 2090 .MSTORE,
   opAt 2091 .SHR,
   pushAt 2092 2 1698,
   opAt 2093 .MLOAD,
   opAt 2094 (.Swap ⟨0, by decide⟩)]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3380). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2459 .JUMPDEST,
   opAt 2460 .POP,
   pushAt 2461 2 1760,
   opAt 2462 .MLOAD,
   opAt 2463 .ISZERO,
   pushAt 2464 2 5518,
   opAt 2465 .JUMPI]

/-- The cleanup tail (pcs 5444-5465): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4409 .JUMPDEST,
   opAt 4410 .POP,
   opAt 4411 .POP,
   opAt 4412 .POP,
   opAt 4413 .POP,
   opAt 4414 .POP,
   opAt 4415 .POP,
   opAt 4416 .POP,
   opAt 4417 .POP,
   opAt 4418 .POP,
   opAt 4419 .POP,
   opAt 4420 .POP,
   opAt 4421 .POP,
   opAt 4422 .POP,
   opAt 4423 .POP,
   opAt 4424 .POP,
   opAt 4425 .POP,
   pushAt 4426 2 2317,
   opAt 4427 .ADD,
   opAt 4428 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
