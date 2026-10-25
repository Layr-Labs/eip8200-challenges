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
   opAt 1880 .XOR,
   opAt 1881 .JUMPDEST,
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
   pushAt 1953 1 1,
   opAt 1954 .ADD,
   pushAt 1955 2 1600,
   opAt 1956 .MSTORE,
   pushAt 1957 1 255,
   opAt 1958 .SUB,
   pushAt 1959 2 1536,
   opAt 1960 .MSTORE,
   opAt 1961 (.Dup ⟨0, by decide⟩),
   opAt 1962 (.Dup ⟨2, by decide⟩),
   opAt 1963 .DIV,
   opAt 1964 (.Dup ⟨0, by decide⟩),
   pushAt 1965 2 1568,
   opAt 1966 .MSTORE,
   opAt 1967 (.Dup ⟨0, by decide⟩),
   opAt 1968 (.Dup ⟨0, by decide⟩),
   pushAt 1969 0 0,
   opAt 1970 .SUB,
   opAt 1971 .MOD,
   pushAt 1972 2 1632,
   opAt 1973 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1974 2 2752,
   opAt 1975 .MLOAD,
   opAt 1976 .MLOAD,
   opAt 1977 (.Dup ⟨0, by decide⟩),
   opAt 1978 (.Dup ⟨2, by decide⟩),
   opAt 1979 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1980 (.Dup ⟨0, by decide⟩),
   pushAt 1981 1 3,
   opAt 1982 .MUL,
   pushAt 1983 1 2,
   opAt 1984 .XOR,
   opAt 1985 (.Dup ⟨0, by decide⟩),
   opAt 1986 (.Dup ⟨2, by decide⟩),
   opAt 1987 .MUL,
   pushAt 1988 1 2,
   opAt 1989 .SUB,
   opAt 1990 .MUL,
   opAt 1991 (.Dup ⟨0, by decide⟩),
   opAt 1992 (.Dup ⟨2, by decide⟩),
   opAt 1993 .MUL,
   pushAt 1994 1 2,
   opAt 1995 .SUB,
   opAt 1996 .MUL,
   opAt 1997 (.Dup ⟨0, by decide⟩),
   opAt 1998 (.Dup ⟨2, by decide⟩),
   opAt 1999 .MUL,
   pushAt 2000 1 2,
   opAt 2001 .SUB,
   opAt 2002 .MUL,
   opAt 2003 (.Dup ⟨0, by decide⟩),
   opAt 2004 (.Dup ⟨2, by decide⟩),
   opAt 2005 .MUL,
   pushAt 2006 1 2,
   opAt 2007 .SUB,
   opAt 2008 .MUL,
   opAt 2009 (.Dup ⟨0, by decide⟩),
   opAt 2010 (.Dup ⟨2, by decide⟩),
   opAt 2011 .MUL,
   pushAt 2012 1 2,
   opAt 2013 .SUB,
   opAt 2014 .MUL,
   opAt 2015 (.Dup ⟨0, by decide⟩),
   opAt 2016 (.Dup ⟨2, by decide⟩),
   opAt 2017 .MUL,
   pushAt 2018 1 2,
   opAt 2019 .SUB,
   opAt 2020 .MUL,
   opAt 2021 (.Swap ⟨0, by decide⟩),
   opAt 2022 .POP]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2023 (.Dup ⟨1, by decide⟩),
   opAt 2024 (.Dup ⟨1, by decide⟩),
   opAt 2025 .MUL,
   pushAt 2026 2 1664,
   opAt 2027 .MSTORE,
   opAt 2028 (.Dup ⟨2, by decide⟩),
   opAt 2029 .MUL,
   pushAt 2030 0 0,
   opAt 2031 .SUB,
   pushAt 2032 2 2720,
   opAt 2033 .MSTORE,
   opAt 2034 .POP,
   opAt 2035 .POP,
   opAt 2036 .POP,
   opAt 2037 .POP,
   pushAt 2038 0 0,
   pushAt 2039 0 0,
   opAt 2040 (.Dup ⟨4, by decide⟩),
   opAt 2041 (.Dup ⟨4, by decide⟩),
   opAt 2042 (.Dup ⟨7, by decide⟩),
   pushAt 2043 2 1536,
   opAt 2044 .MLOAD,
   pushAt 2045 2 1568,
   opAt 2046 .MLOAD,
   pushAt 2047 2 1664,
   opAt 2048 .MLOAD,
   pushAt 2049 2 1632,
   opAt 2050 .MLOAD,
   pushAt 2051 2 1504,
   opAt 2052 .MLOAD,
   pushAt 2053 2 1472,
   opAt 2054 .MLOAD,
   pushAt 2055 2 1440,
   opAt 2056 .MLOAD,
   pushAt 2057 2 1408,
   opAt 2058 .MLOAD,
   pushAt 2059 2 1376,
   opAt 2060 .MLOAD,
   pushAt 2061 2 1344,
   opAt 2062 .MLOAD,
   pushAt 2063 2 1312,
   opAt 2064 .MLOAD,
   opAt 2065 (.Dup ⟨12, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2091 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2092 (.Dup ⟨15, by decide⟩),
   pushAt 2093 2 2112,
   pushAt 2094 2 2080,
   opAt 2095 .MCOPY,
   pushAt 2096 0 0,
   pushAt 2097 2 2784,
   opAt 2098 .MLOAD,
   opAt 2099 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2100 2 2080,
   opAt 2101 .MLOAD,
   opAt 2102 (.Dup ⟨0, by decide⟩),
   opAt 2103 (.Dup ⟨14, by decide⟩),
   opAt 2104 .SHR,
   opAt 2105 (.Swap ⟨0, by decide⟩),
   pushAt 2106 2 1600,
   opAt 2107 .MLOAD,
   opAt 2108 .SHL,
   pushAt 2109 2 2112,
   opAt 2110 .MLOAD,
   opAt 2111 (.Dup ⟨15, by decide⟩),
   opAt 2112 .SHR,
   opAt 2113 .ADD,
   opAt 2114 (.Dup ⟨13, by decide⟩),
   opAt 2115 (.Dup ⟨0, by decide⟩),
   opAt 2116 (.Dup ⟨13, by decide⟩),
   opAt 2117 (.Dup ⟨4, by decide⟩),
   opAt 2118 .MULMOD,
   opAt 2119 (.Dup ⟨2, by decide⟩),
   opAt 2120 .ADDMOD,
   opAt 2121 (.Swap ⟨0, by decide⟩),
   opAt 2122 .SUB,
   opAt 2123 (.Dup ⟨12, by decide⟩),
   opAt 2124 .MUL,
   opAt 2125 (.Dup ⟨0, by decide⟩),
   pushAt 2126 0 0,
   opAt 2127 .MLOAD,
   opAt 2128 .MUL,
   pushAt 2129 2 2112,
   opAt 2130 .MLOAD,
   opAt 2131 .SUB,
   pushAt 2132 1 32,
   opAt 2133 .MLOAD,
   pushAt 2134 1 128,
   opAt 2135 .SHR,
   opAt 2136 (.Dup ⟨2, by decide⟩),
   pushAt 2137 1 128,
   opAt 2138 .SHR,
   opAt 2139 .MUL,
   opAt 2140 .GT,
   opAt 2141 (.Swap ⟨0, by decide⟩),
   opAt 2142 .SUB,
   pushAt 2143 0 0,
   opAt 2144 .NOT,
   opAt 2145 (.Swap ⟨1, by decide⟩),
   opAt 2146 (.Dup ⟨14, by decide⟩),
   opAt 2147 .GT,
   opAt 2148 (.Dup ⟨2, by decide⟩),
   opAt 2149 .ADD,
   opAt 2150 .OR,
   opAt 2151 .JUMPDEST]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2372 2 2080,
   opAt 2373 .MLOAD,
   opAt 2374 (.Dup ⟨1, by decide⟩),
   opAt 2375 .ADD,
   opAt 2376 (.Dup ⟨0, by decide⟩),
   opAt 2377 (.Swap ⟨1, by decide⟩),
   opAt 2378 .GT,
   opAt 2379 (.Dup ⟨1, by decide⟩),
   opAt 2380 (.Dup ⟨3, by decide⟩),
   opAt 2381 .GT,
   opAt 2382 .GT,
   opAt 2383 (.Swap ⟨2, by decide⟩),
   opAt 2384 .POP,
   opAt 2385 .SUB,
   opAt 2386 (.Dup ⟨0, by decide⟩),
   pushAt 2387 2 2080,
   opAt 2388 .MSTORE,
   opAt 2389 (.Dup ⟨1, by decide⟩),
   opAt 2390 .OR,
   pushAt 2391 2 3073,
   opAt 2392 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2401 .JUMPDEST,
   opAt 2402 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2403 .JUMPDEST,
   pushAt 2404 0 0,
   pushAt 2405 2 2784,
   opAt 2406 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2407 .JUMPDEST,
   opAt 2408 (.Dup ⟨0, by decide⟩),
   opAt 2409 .MLOAD,
   pushAt 2410 2 2112,
   opAt 2411 (.Dup ⟨2, by decide⟩),
   opAt 2412 .SUB,
   opAt 2413 .MLOAD,
   opAt 2414 (.Dup ⟨1, by decide⟩),
   opAt 2415 .ADD,
   opAt 2416 (.Swap ⟨0, by decide⟩),
   opAt 2417 (.Dup ⟨1, by decide⟩),
   opAt 2418 .LT,
   opAt 2419 (.Swap ⟨0, by decide⟩),
   opAt 2420 (.Dup ⟨3, by decide⟩),
   opAt 2421 .ADD,
   opAt 2422 (.Swap ⟨2, by decide⟩),
   opAt 2423 (.Dup ⟨3, by decide⟩),
   opAt 2424 .LT,
   opAt 2425 .OR,
   opAt 2426 (.Swap ⟨1, by decide⟩),
   opAt 2427 (.Dup ⟨1, by decide⟩),
   opAt 2428 .MSTORE,
   pushAt 2429 1 31,
   opAt 2430 .NOT,
   opAt 2431 .ADD,
   pushAt 2432 2 2111,
   opAt 2433 (.Dup ⟨1, by decide⟩),
   opAt 2434 .GT,
   pushAt 2435 2 3081,
   opAt 2436 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2437 .POP,
   pushAt 2438 2 2080,
   opAt 2439 .MLOAD,
   opAt 2440 (.Dup ⟨1, by decide⟩),
   opAt 2441 .ADD,
   opAt 2442 (.Dup ⟨0, by decide⟩),
   pushAt 2443 2 2080,
   opAt 2444 .MSTORE,
   opAt 2445 .LT,
   opAt 2446 .ISZERO,
   pushAt 2447 2 3075,
   opAt 2448 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2449 2 2080,
   opAt 2450 .MLOAD,
   opAt 2451 (.Dup ⟨0, by decide⟩),
   opAt 2452 .ISZERO,
   pushAt 2453 2 3061,
   opAt 2454 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2393 .JUMPDEST,
   opAt 2394 .NOT,
   opAt 2395 .ADD,
   opAt 2396 (.Dup ⟨0, by decide⟩),
   pushAt 2397 2 2704,
   opAt 2398 .JUMPI]

/-- The loop exit after the last step: jump to `SHIFT_DONE`. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2399 2 3146,
   opAt 2400 .JUMP]

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
  CycleSubmission.Global.Binding.jumpDest 2091 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3075 = true :=
  CycleSubmission.Global.Binding.jumpDest 2403 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3081 = true :=
  CycleSubmission.Global.Binding.jumpDest 2407 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3073 = true :=
  CycleSubmission.Global.Binding.jumpDest 2401 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3061 = true :=
  CycleSubmission.Global.Binding.jumpDest 2393 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3146 = true :=
  CycleSubmission.Global.Binding.jumpDest 2455 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3944 = true :=
  CycleSubmission.Global.Binding.jumpDest 3043 (by rfl)

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
  [opAt 2066 (.Dup ⟨0, by decide⟩),
   pushAt 2067 1 29,
   opAt 2068 .MUL,
   pushAt 2069 5 3017,
   opAt 2070 .SUB,
   pushAt 2071 2 1698,
   opAt 2072 .MSTORE,
   opAt 2073 (.Dup ⟨12, by decide⟩),
   pushAt 2074 1 1,
   opAt 2075 .EQ,
   pushAt 2076 2 2656,
   opAt 2077 .MLOAD,
   opAt 2078 .CALLDATALOAD,
   pushAt 2079 0 0,
   opAt 2080 .BYTE,
   pushAt 2081 1 3,
   opAt 2082 .EQ,
   opAt 2083 .AND,
   opAt 2084 (.Dup ⟨0, by decide⟩),
   pushAt 2085 2 1760,
   opAt 2086 .MSTORE,
   opAt 2087 .SHR,
   pushAt 2088 2 1698,
   opAt 2089 .MLOAD,
   opAt 2090 (.Swap ⟨0, by decide⟩)]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3380). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2455 .JUMPDEST,
   opAt 2456 .POP,
   pushAt 2457 2 1760,
   opAt 2458 .MLOAD,
   opAt 2459 .ISZERO,
   pushAt 2460 2 3944,
   opAt 2461 .JUMPI]

/-- The cleanup tail (pcs 3866-3887): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3043 .JUMPDEST,
   opAt 3044 .POP,
   opAt 3045 .POP,
   opAt 3046 .POP,
   opAt 3047 .POP,
   opAt 3048 .POP,
   opAt 3049 .POP,
   opAt 3050 .POP,
   opAt 3051 .POP,
   opAt 3052 .POP,
   opAt 3053 .POP,
   opAt 3054 .POP,
   opAt 3055 .POP,
   opAt 3056 .POP,
   opAt 3057 .POP,
   opAt 3058 .POP,
   opAt 3059 .POP,
   pushAt 3060 2 2317,
   opAt 3061 .ADD,
   opAt 3062 .JUMP]

end CycleSubmission.Global.Fast
