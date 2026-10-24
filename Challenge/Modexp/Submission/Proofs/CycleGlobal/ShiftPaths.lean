import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace CycleSubmission.Global.Fast
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast


open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The dispatcher guard (k2465): `bsize = 32 n` or jump straight to `modexpBig` (pc 219). -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1877 .JUMPDEST,
   opAt 1878 (.Dup ⟨0, by decide⟩),
   opAt 1879 (.Dup ⟨3, by decide⟩),
   opAt 1880 .EQ,
   opAt 1881 .ISZERO,
   pushAt 1882 1 219,
   opAt 1883 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1884 (.Dup ⟨0, by decide⟩),
   pushAt 1885 1 96,
   pushAt 1886 2 2112,
   opAt 1887 .CALLDATACOPY,
   pushAt 1888 2 2412,
   pushAt 1889 2 3493,
   opAt 1890 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1896 (.Dup ⟨0, by decide⟩),
   pushAt 1897 1 128,
   opAt 1898 .EQ,
   pushAt 1899 2 2336,
   opAt 1900 .JUMPI]

/-- Negation cell at pc 2429: `NEG[1504] := 0 - mem[224]`. -/
def negS8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1901 1 224,
   opAt 1902 .MLOAD,
   pushAt 1903 0 0,
   opAt 1904 .SUB,
   pushAt 1905 2 1504,
   opAt 1906 .MSTORE]

/-- Negation cell at pc 2438: `NEG[1472] := NOT mem[192]`. -/
def negN8a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1907 1 192,
   opAt 1908 .MLOAD,
   opAt 1909 .NOT,
   pushAt 1910 2 1472,
   opAt 1911 .MSTORE]

/-- Negation cell at pc 2446: `NEG[1440] := NOT mem[160]`. -/
def negN8b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1912 1 160,
   opAt 1913 .MLOAD,
   opAt 1914 .NOT,
   pushAt 1915 2 1440,
   opAt 1916 .MSTORE]

/-- Negation cell at pc 2454: `NEG[1408] := NOT mem[128]`. -/
def negN8c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1917 1 128,
   opAt 1918 .MLOAD,
   opAt 1919 .NOT,
   pushAt 1920 2 1408,
   opAt 1921 .MSTORE]

/-- Negation cell at pc 2462: `NEG[1376] := NOT mem[96]`. -/
def negN8d :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1922 1 96,
   opAt 1923 .MLOAD,
   opAt 1924 .NOT,
   pushAt 1925 2 1376,
   opAt 1926 .MSTORE]

/-- Negation cell at pc 2471: `NEG[1344] := NOT mem[64]`. -/
def negNTa :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1928 1 64,
   opAt 1929 .MLOAD,
   opAt 1930 .NOT,
   pushAt 1931 2 1344,
   opAt 1932 .MSTORE]

/-- Negation cell at pc 2479: `NEG[1312] := NOT mem[32]`. -/
def negNTb :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1933 1 32,
   opAt 1934 .MLOAD,
   opAt 1935 .NOT,
   pushAt 1936 2 1312,
   opAt 1937 .MSTORE]

/-- Negation cell at pc 2487: `NEG[1280] := NOT mem[0]`. -/
def negNTc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1938 0 0,
   opAt 1939 .MLOAD,
   opAt 1940 .NOT,
   pushAt 1941 2 1280,
   opAt 1942 .MSTORE]

/-- Negation cell at pc 2337: `NEG[1376] := 0 - mem[96]`. -/
def negS4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1848 1 96,
   opAt 1849 .MLOAD,
   pushAt 1850 0 0,
   opAt 1851 .SUB,
   pushAt 1852 2 1376,
   opAt 1853 .MSTORE]

/-- The four-limb stub's `JUMPDEST` (pc 2336). -/
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1847 .JUMPDEST]

/-- The four-limb stub joins `NEG_TAIL` (pc 2470). -/
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1854 2 2470,
   opAt 1855 .JUMP]

/-- `NEG_TAIL`'s `JUMPDEST` (pc 2470). -/
def negJT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1927 .JUMPDEST]

/-- Eight-limb negation cells 7..3 (limb 7: `0 - m_7`), falling into `NEG_TAIL`. -/
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

/-- Four-limb negation stub (pc 2336): limb 3 as `0 - m_3`, then `NEG_TAIL` at pc 2470. -/
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

/-- `NEG_TAIL` (pc 2470): negation cells 2..0. -/
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  negJT ++ negNTa ++ negNTb ++ negNTc

/-- `blk2919`, first part: `L = d &&& -d` twice on top of `d`, stopping before the `CLZ`. -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1943 0 0,
   opAt 1944 .MLOAD,
   opAt 1945 (.Dup ⟨0, by decide⟩),
   pushAt 1946 0 0,
   opAt 1947 .SUB,
   opAt 1948 (.Dup ⟨1, by decide⟩),
   opAt 1949 .AND,
   opAt 1950 (.Dup ⟨0, by decide⟩)]

/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1952 (.Dup ⟨0, by decide⟩),
   opAt 1953 .NOT,
   pushAt 1954 0 0,
   opAt 1955 .SUB,
   pushAt 1956 2 1600,
   opAt 1957 .MSTORE,
   pushAt 1958 1 255,
   opAt 1959 .SUB,
   pushAt 1960 2 1536,
   opAt 1961 .MSTORE,
   opAt 1962 (.Dup ⟨0, by decide⟩),
   opAt 1963 (.Dup ⟨2, by decide⟩),
   opAt 1964 .DIV,
   opAt 1965 (.Dup ⟨0, by decide⟩),
   pushAt 1966 2 1568,
   opAt 1967 .MSTORE,
   opAt 1968 (.Dup ⟨0, by decide⟩),
   opAt 1969 (.Dup ⟨0, by decide⟩),
   pushAt 1970 0 0,
   opAt 1971 .SUB,
   opAt 1972 .MOD,
   pushAt 1973 2 1632,
   opAt 1974 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1975 2 2752,
   opAt 1976 .MLOAD,
   opAt 1977 .MLOAD,
   opAt 1978 (.Dup ⟨0, by decide⟩),
   opAt 1979 (.Dup ⟨2, by decide⟩),
   opAt 1980 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1981 (.Dup ⟨0, by decide⟩),
   pushAt 1982 1 3,
   opAt 1983 .MUL,
   pushAt 1984 1 2,
   opAt 1985 .XOR,
   opAt 1986 (.Dup ⟨0, by decide⟩),
   opAt 1987 (.Dup ⟨2, by decide⟩),
   opAt 1988 .MUL,
   pushAt 1989 1 2,
   opAt 1990 .SUB,
   opAt 1991 .MUL,
   opAt 1992 (.Dup ⟨0, by decide⟩),
   opAt 1993 (.Dup ⟨2, by decide⟩),
   opAt 1994 .MUL,
   pushAt 1995 1 2,
   opAt 1996 .SUB,
   opAt 1997 .MUL,
   opAt 1998 (.Dup ⟨0, by decide⟩),
   opAt 1999 (.Dup ⟨2, by decide⟩),
   opAt 2000 .MUL,
   pushAt 2001 1 2,
   opAt 2002 .SUB,
   opAt 2003 .MUL,
   opAt 2004 (.Dup ⟨0, by decide⟩),
   opAt 2005 (.Dup ⟨2, by decide⟩),
   opAt 2006 .MUL,
   pushAt 2007 1 2,
   opAt 2008 .SUB,
   opAt 2009 .MUL,
   opAt 2010 (.Dup ⟨0, by decide⟩),
   opAt 2011 (.Dup ⟨2, by decide⟩),
   opAt 2012 .MUL,
   pushAt 2013 1 2,
   opAt 2014 .SUB,
   opAt 2015 .MUL,
   opAt 2016 (.Dup ⟨0, by decide⟩),
   opAt 2017 (.Dup ⟨2, by decide⟩),
   opAt 2018 .MUL,
   pushAt 2019 1 2,
   opAt 2020 .SUB,
   opAt 2021 .MUL,
   opAt 2022 (.Swap ⟨0, by decide⟩),
   opAt 2023 .POP]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2024 (.Dup ⟨1, by decide⟩),
   opAt 2025 (.Dup ⟨1, by decide⟩),
   opAt 2026 .MUL,
   pushAt 2027 2 1664,
   opAt 2028 .MSTORE,
   opAt 2029 (.Dup ⟨2, by decide⟩),
   opAt 2030 .MUL,
   pushAt 2031 0 0,
   opAt 2032 .SUB,
   pushAt 2033 2 2720,
   opAt 2034 .MSTORE,
   opAt 2035 .POP,
   opAt 2036 .POP,
   opAt 2037 .POP,
   opAt 2038 .POP,
   pushAt 2039 0 0,
   pushAt 2040 0 0,
   opAt 2041 (.Dup ⟨4, by decide⟩),
   opAt 2042 (.Dup ⟨4, by decide⟩),
   opAt 2043 (.Dup ⟨7, by decide⟩),
   pushAt 2044 2 1536,
   opAt 2045 .MLOAD,
   pushAt 2046 2 1568,
   opAt 2047 .MLOAD,
   pushAt 2048 2 1664,
   opAt 2049 .MLOAD,
   pushAt 2050 2 1632,
   opAt 2051 .MLOAD,
   pushAt 2052 2 1504,
   opAt 2053 .MLOAD,
   pushAt 2054 2 1472,
   opAt 2055 .MLOAD,
   pushAt 2056 2 1440,
   opAt 2057 .MLOAD,
   pushAt 2058 2 1408,
   opAt 2059 .MLOAD,
   pushAt 2060 2 1376,
   opAt 2061 .MLOAD,
   pushAt 2062 2 1344,
   opAt 2063 .MLOAD,
   pushAt 2064 2 1312,
   opAt 2065 .MLOAD,
   opAt 2066 (.Dup ⟨12, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2092 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2093 (.Dup ⟨15, by decide⟩),
   pushAt 2094 2 2112,
   pushAt 2095 2 2080,
   opAt 2096 .MCOPY,
   pushAt 2097 0 0,
   pushAt 2098 2 2784,
   opAt 2099 .MLOAD,
   opAt 2100 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2101 2 2080,
   opAt 2102 .MLOAD,
   opAt 2103 (.Dup ⟨0, by decide⟩),
   opAt 2104 (.Dup ⟨14, by decide⟩),
   opAt 2105 .SHR,
   opAt 2106 (.Swap ⟨0, by decide⟩),
   pushAt 2107 2 1600,
   opAt 2108 .MLOAD,
   opAt 2109 .SHL,
   pushAt 2110 2 2112,
   opAt 2111 .MLOAD,
   opAt 2112 (.Dup ⟨15, by decide⟩),
   opAt 2113 .SHR,
   opAt 2114 .ADD,
   opAt 2115 (.Dup ⟨13, by decide⟩),
   opAt 2116 (.Dup ⟨0, by decide⟩),
   opAt 2117 (.Dup ⟨13, by decide⟩),
   opAt 2118 (.Dup ⟨4, by decide⟩),
   opAt 2119 .MULMOD,
   opAt 2120 (.Dup ⟨2, by decide⟩),
   opAt 2121 .ADDMOD,
   opAt 2122 (.Swap ⟨0, by decide⟩),
   opAt 2123 .SUB,
   opAt 2124 (.Dup ⟨12, by decide⟩),
   opAt 2125 .MUL,
   opAt 2126 (.Dup ⟨0, by decide⟩),
   pushAt 2127 0 0,
   opAt 2128 .MLOAD,
   opAt 2129 .MUL,
   pushAt 2130 2 2112,
   opAt 2131 .MLOAD,
   opAt 2132 .SUB,
   pushAt 2133 1 32,
   opAt 2134 .MLOAD,
   pushAt 2135 1 128,
   opAt 2136 .SHR,
   opAt 2137 (.Dup ⟨2, by decide⟩),
   pushAt 2138 1 128,
   opAt 2139 .SHR,
   opAt 2140 .MUL,
   opAt 2141 .GT,
   opAt 2142 (.Swap ⟨0, by decide⟩),
   opAt 2143 .SUB,
   pushAt 2144 0 0,
   opAt 2145 .NOT,
   opAt 2146 (.Swap ⟨1, by decide⟩),
   opAt 2147 (.Dup ⟨14, by decide⟩),
   opAt 2148 .GT,
   opAt 2149 .ISZERO,
   pushAt 2150 0 0,
   opAt 2151 .SUB,
   opAt 2152 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2373 2 2080,
   opAt 2374 .MLOAD,
   opAt 2375 (.Dup ⟨1, by decide⟩),
   opAt 2376 .ADD,
   opAt 2377 (.Dup ⟨0, by decide⟩),
   opAt 2378 (.Swap ⟨1, by decide⟩),
   opAt 2379 .GT,
   opAt 2380 (.Dup ⟨1, by decide⟩),
   opAt 2381 (.Dup ⟨3, by decide⟩),
   opAt 2382 .GT,
   opAt 2383 .GT,
   opAt 2384 (.Swap ⟨2, by decide⟩),
   opAt 2385 .POP,
   opAt 2386 .SUB,
   opAt 2387 (.Dup ⟨0, by decide⟩),
   pushAt 2388 2 2080,
   opAt 2389 .MSTORE,
   opAt 2390 (.Dup ⟨1, by decide⟩),
   opAt 2391 .OR,
   pushAt 2392 2 3073,
   opAt 2393 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2402 .JUMPDEST,
   opAt 2403 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2404 .JUMPDEST,
   pushAt 2405 0 0,
   pushAt 2406 2 2784,
   opAt 2407 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2408 .JUMPDEST,
   opAt 2409 (.Dup ⟨0, by decide⟩),
   opAt 2410 .MLOAD,
   pushAt 2411 2 2112,
   opAt 2412 (.Dup ⟨2, by decide⟩),
   opAt 2413 .SUB,
   opAt 2414 .MLOAD,
   opAt 2415 (.Dup ⟨1, by decide⟩),
   opAt 2416 .ADD,
   opAt 2417 (.Swap ⟨0, by decide⟩),
   opAt 2418 (.Dup ⟨1, by decide⟩),
   opAt 2419 .LT,
   opAt 2420 (.Swap ⟨0, by decide⟩),
   opAt 2421 (.Dup ⟨3, by decide⟩),
   opAt 2422 .ADD,
   opAt 2423 (.Swap ⟨2, by decide⟩),
   opAt 2424 (.Dup ⟨3, by decide⟩),
   opAt 2425 .LT,
   opAt 2426 .OR,
   opAt 2427 (.Swap ⟨1, by decide⟩),
   opAt 2428 (.Dup ⟨1, by decide⟩),
   opAt 2429 .MSTORE,
   pushAt 2430 1 31,
   opAt 2431 .NOT,
   opAt 2432 .ADD,
   pushAt 2433 2 2111,
   opAt 2434 (.Dup ⟨1, by decide⟩),
   opAt 2435 .GT,
   pushAt 2436 2 3081,
   opAt 2437 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2438 .POP,
   pushAt 2439 2 2080,
   opAt 2440 .MLOAD,
   opAt 2441 (.Dup ⟨1, by decide⟩),
   opAt 2442 .ADD,
   opAt 2443 (.Dup ⟨0, by decide⟩),
   pushAt 2444 2 2080,
   opAt 2445 .MSTORE,
   opAt 2446 .LT,
   opAt 2447 .ISZERO,
   pushAt 2448 2 3075,
   opAt 2449 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2450 2 2080,
   opAt 2451 .MLOAD,
   opAt 2452 (.Dup ⟨0, by decide⟩),
   opAt 2453 .ISZERO,
   pushAt 2454 2 3061,
   opAt 2455 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2394 .JUMPDEST,
   opAt 2395 .NOT,
   opAt 2396 .ADD,
   opAt 2397 (.Dup ⟨0, by decide⟩),
   pushAt 2398 2 2704,
   opAt 2399 .JUMPI]

/-- The loop exit after the last step: jump to `SHIFT_DONE`. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2400 2 3146,
   opAt 2401 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2390 = true :=
  CycleSubmission.Global.Binding.jumpDest 1877 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 219 = true :=
  CycleSubmission.Global.Binding.jumpDest 146 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2412 = true :=
  CycleSubmission.Global.Binding.jumpDest 1891 (by rfl)


theorem jumpDestNeg4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2336 = true :=
  CycleSubmission.Global.Binding.jumpDest 1847 (by rfl)

theorem jumpDestNegT :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2470 = true :=
  CycleSubmission.Global.Binding.jumpDest 1927 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2704 = true :=
  CycleSubmission.Global.Binding.jumpDest 2092 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3075 = true :=
  CycleSubmission.Global.Binding.jumpDest 2404 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3081 = true :=
  CycleSubmission.Global.Binding.jumpDest 2408 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3073 = true :=
  CycleSubmission.Global.Binding.jumpDest 2402 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3061 = true :=
  CycleSubmission.Global.Binding.jumpDest 2394 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3146 = true :=
  CycleSubmission.Global.Binding.jumpDest 2456 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3944 = true :=
  CycleSubmission.Global.Binding.jumpDest 3053 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2329 = true :=
  CycleSubmission.Global.Binding.jumpDest 1843 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2946 + 116·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2067 (.Dup ⟨0, by decide⟩),
   pushAt 2068 1 29,
   opAt 2069 .MUL,
   pushAt 2070 5 3017,
   opAt 2071 .SUB,
   pushAt 2072 2 1698,
   opAt 2073 .MSTORE,
   opAt 2074 (.Dup ⟨12, by decide⟩),
   pushAt 2075 1 1,
   opAt 2076 .EQ,
   pushAt 2077 2 2656,
   opAt 2078 .MLOAD,
   opAt 2079 .CALLDATALOAD,
   pushAt 2080 0 0,
   opAt 2081 .BYTE,
   pushAt 2082 1 3,
   opAt 2083 .EQ,
   opAt 2084 .AND,
   opAt 2085 (.Dup ⟨0, by decide⟩),
   pushAt 2086 2 1760,
   opAt 2087 .MSTORE,
   opAt 2088 .SHR,
   pushAt 2089 2 1698,
   opAt 2090 .MLOAD,
   opAt 2091 (.Swap ⟨0, by decide⟩)]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3380). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2456 .JUMPDEST,
   opAt 2457 .POP,
   pushAt 2458 2 1760,
   opAt 2459 .MLOAD,
   opAt 2460 .ISZERO,
   pushAt 2461 2 3944,
   opAt 2462 .JUMPI]

/-- The cleanup tail (pcs 3866-3887): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3053 .JUMPDEST,
   opAt 3054 .POP,
   opAt 3055 .POP,
   opAt 3056 .POP,
   opAt 3057 .POP,
   opAt 3058 .POP,
   opAt 3059 .POP,
   opAt 3060 .POP,
   opAt 3061 .POP,
   opAt 3062 .POP,
   opAt 3063 .POP,
   opAt 3064 .POP,
   opAt 3065 .POP,
   opAt 3066 .POP,
   opAt 3067 .POP,
   opAt 3068 .POP,
   opAt 3069 .POP,
   pushAt 3070 2 2317,
   opAt 3071 .ADD,
   opAt 3072 .JUMP]

end CycleSubmission.Global.Fast
