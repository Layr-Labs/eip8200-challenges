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
  [opAt 1873 .JUMPDEST,
   opAt 1874 (.Dup ⟨0, by decide⟩),
   opAt 1875 (.Dup ⟨3, by decide⟩),
   opAt 1876 .XOR,
   pushAt 1877 2 219,
   opAt 1878 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1879 (.Dup ⟨0, by decide⟩),
   pushAt 1880 1 96,
   pushAt 1881 2 2112,
   opAt 1882 .CALLDATACOPY,
   pushAt 1883 2 2412,
   pushAt 1884 2 3493,
   opAt 1885 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1891 (.Dup ⟨0, by decide⟩),
   pushAt 1892 1 128,
   opAt 1893 .EQ,
   pushAt 1894 2 2336,
   opAt 1895 .JUMPI]

/-- Negation cell at pc 2429: `NEG[1504] := 0 - mem[224]`. -/
def negS8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1896 1 224,
   opAt 1897 .MLOAD,
   pushAt 1898 0 0,
   opAt 1899 .SUB,
   pushAt 1900 2 1504,
   opAt 1901 .MSTORE]

/-- Negation cell at pc 2438: `NEG[1472] := NOT mem[192]`. -/
def negN8a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1902 1 192,
   opAt 1903 .MLOAD,
   opAt 1904 .NOT,
   pushAt 1905 2 1472,
   opAt 1906 .MSTORE]

/-- Negation cell at pc 2446: `NEG[1440] := NOT mem[160]`. -/
def negN8b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1907 1 160,
   opAt 1908 .MLOAD,
   opAt 1909 .NOT,
   pushAt 1910 2 1440,
   opAt 1911 .MSTORE]

/-- Negation cell at pc 2454: `NEG[1408] := NOT mem[128]`. -/
def negN8c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1912 1 128,
   opAt 1913 .MLOAD,
   opAt 1914 .NOT,
   pushAt 1915 2 1408,
   opAt 1916 .MSTORE]

/-- Negation cell at pc 2462: `NEG[1376] := NOT mem[96]`. -/
def negN8d :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1917 1 96,
   opAt 1918 .MLOAD,
   opAt 1919 .NOT,
   pushAt 1920 2 1376,
   opAt 1921 .MSTORE]

/-- Negation cell at pc 2471: `NEG[1344] := NOT mem[64]`. -/
def negNTa :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1923 1 64,
   opAt 1924 .MLOAD,
   opAt 1925 .NOT,
   pushAt 1926 2 1344,
   opAt 1927 .MSTORE]

/-- Negation cell at pc 2479: `NEG[1312] := NOT mem[32]`. -/
def negNTb :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1928 1 32,
   opAt 1929 .MLOAD,
   opAt 1930 .NOT,
   pushAt 1931 2 1312,
   opAt 1932 .MSTORE]

/-- Negation cell at pc 2487: `NEG[1280] := NOT mem[0]`. -/
def negNTc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1933 0 0,
   opAt 1934 .MLOAD,
   opAt 1935 .NOT,
   pushAt 1936 2 1280,
   opAt 1937 .MSTORE]

/-- Negation cell at pc 2337: `NEG[1376] := 0 - mem[96]`. -/
def negS4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1844 1 96,
   opAt 1845 .MLOAD,
   pushAt 1846 0 0,
   opAt 1847 .SUB,
   pushAt 1848 2 1376,
   opAt 1849 .MSTORE]

/-- The four-limb stub's `JUMPDEST` (pc 2336). -/
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1843 .JUMPDEST]

/-- The four-limb stub joins `NEG_TAIL` (pc 2470). -/
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1850 2 2470,
   opAt 1851 .JUMP]

/-- `NEG_TAIL`'s `JUMPDEST` (pc 2470). -/
def negJT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1922 .JUMPDEST]

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
  [pushAt 1938 0 0,
   opAt 1939 .MLOAD,
   opAt 1940 (.Dup ⟨0, by decide⟩),
   pushAt 1941 0 0,
   opAt 1942 .SUB,
   opAt 1943 (.Dup ⟨1, by decide⟩),
   opAt 1944 .AND,
   opAt 1945 (.Dup ⟨0, by decide⟩)]

/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1947 (.Dup ⟨0, by decide⟩),
   pushAt 1948 1 1,
   opAt 1949 .ADD,
   pushAt 1950 2 1600,
   opAt 1951 .MSTORE,
   pushAt 1952 1 255,
   opAt 1953 .SUB,
   pushAt 1954 3 1536,
   opAt 1955 .MSTORE,
   opAt 1956 (.Dup ⟨1, by decide⟩),
   opAt 1957 .DIV,
   opAt 1958 (.Dup ⟨0, by decide⟩),
   pushAt 1959 2 1568,
   opAt 1960 .MSTORE,
   opAt 1961 (.Dup ⟨0, by decide⟩),
   opAt 1962 (.Dup ⟨0, by decide⟩),
   pushAt 1963 0 0,
   opAt 1964 .SUB,
   opAt 1965 .MOD,
   pushAt 1966 2 1632,
   opAt 1967 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1968 2 2752,
   opAt 1969 .MLOAD,
   opAt 1970 .MLOAD,
   opAt 1971 (.Dup ⟨0, by decide⟩),
   opAt 1972 (.Dup ⟨2, by decide⟩),
   opAt 1973 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1974 (.Dup ⟨0, by decide⟩),
   pushAt 1975 1 3,
   opAt 1976 .MUL,
   pushAt 1977 1 2,
   opAt 1978 .XOR,
   opAt 1979 (.Dup ⟨0, by decide⟩),
   opAt 1980 (.Dup ⟨2, by decide⟩),
   opAt 1981 .MUL,
   pushAt 1982 1 2,
   opAt 1983 .SUB,
   opAt 1984 .MUL,
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
   opAt 2010 (.Swap ⟨1, by decide⟩),
   opAt 2011 .MUL,
   pushAt 2012 3 2,
   opAt 2013 .SUB,
   opAt 2014 .MUL]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2015 (.Dup ⟨1, by decide⟩),
   opAt 2016 (.Dup ⟨1, by decide⟩),
   opAt 2017 .MUL,
   pushAt 2018 2 1664,
   opAt 2019 .MSTORE,
   opAt 2020 (.Dup ⟨2, by decide⟩),
   opAt 2021 .MUL,
   pushAt 2022 0 0,
   opAt 2023 .SUB,
   pushAt 2024 3 2720,
   opAt 2025 .MSTORE,
   opAt 2026 .POP,
   opAt 2027 .POP,
   opAt 2028 .POP,
   pushAt 2029 0 0,
   pushAt 2030 0 0,
   opAt 2031 (.Dup ⟨4, by decide⟩),
   opAt 2032 (.Dup ⟨4, by decide⟩),
   opAt 2033 (.Dup ⟨7, by decide⟩),
   pushAt 2034 2 1536,
   opAt 2035 .MLOAD,
   pushAt 2036 2 1568,
   opAt 2037 .MLOAD,
   pushAt 2038 2 1664,
   opAt 2039 .MLOAD,
   pushAt 2040 2 1632,
   opAt 2041 .MLOAD,
   pushAt 2042 2 1504,
   opAt 2043 .MLOAD,
   pushAt 2044 2 1472,
   opAt 2045 .MLOAD,
   pushAt 2046 2 1440,
   opAt 2047 .MLOAD,
   pushAt 2048 2 1408,
   opAt 2049 .MLOAD,
   pushAt 2050 2 1376,
   opAt 2051 .MLOAD,
   pushAt 2052 2 1344,
   opAt 2053 .MLOAD,
   pushAt 2054 2 1312,
   opAt 2055 .MLOAD,
   opAt 2056 (.Dup ⟨12, by decide⟩)]

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
   pushAt 2097 2 2336,
   opAt 2098 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2099 2 2080,
   opAt 2100 .MLOAD,
   opAt 2101 (.Dup ⟨0, by decide⟩),
   opAt 2102 (.Dup ⟨14, by decide⟩),
   opAt 2103 .SHR,
   opAt 2104 (.Swap ⟨0, by decide⟩),
   pushAt 2105 2 1600,
   opAt 2106 .MLOAD,
   opAt 2107 .SHL,
   pushAt 2108 2 2112,
   opAt 2109 .MLOAD,
   opAt 2110 (.Dup ⟨15, by decide⟩),
   opAt 2111 .SHR,
   opAt 2112 .ADD,
   opAt 2113 (.Dup ⟨13, by decide⟩),
   opAt 2114 (.Dup ⟨0, by decide⟩),
   opAt 2115 (.Dup ⟨13, by decide⟩),
   opAt 2116 (.Dup ⟨4, by decide⟩),
   opAt 2117 .MULMOD,
   opAt 2118 (.Dup ⟨2, by decide⟩),
   opAt 2119 .ADDMOD,
   opAt 2120 (.Swap ⟨0, by decide⟩),
   opAt 2121 .SUB,
   opAt 2122 (.Dup ⟨12, by decide⟩),
   opAt 2123 .MUL,
   opAt 2124 (.Dup ⟨15, by decide⟩),
   opAt 2125 (.Dup ⟨1, by decide⟩),
   pushAt 2126 3 128,
   opAt 2127 .SHR,
   opAt 2128 .MUL,
   opAt 2129 (.Dup ⟨1, by decide⟩),
   pushAt 2130 0 0,
   opAt 2131 .MLOAD,
   opAt 2132 .MUL,
   pushAt 2133 2 2112,
   opAt 2134 .MLOAD,
   opAt 2135 .SUB,
   opAt 2136 .LT,
   opAt 2137 (.Swap ⟨0, by decide⟩),
   opAt 2138 .SUB,
   pushAt 2139 0 0,
   opAt 2140 .NOT,
   opAt 2141 (.Swap ⟨1, by decide⟩),
   opAt 2142 (.Dup ⟨14, by decide⟩),
   opAt 2143 .GT,
   opAt 2144 (.Dup ⟨2, by decide⟩),
   opAt 2145 .ADD,
   opAt 2146 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8550 .JUMPDEST]

/-- The appended four-limb loop head (pc 10754): a byte copy of the eight-limb head. -/
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8551 (.Dup ⟨15, by decide⟩),
   pushAt 8552 2 2112,
   pushAt 8553 2 2080,
   opAt 8554 .MCOPY,
   pushAt 8555 0 0,
   pushAt 8556 2 2208,
   opAt 8557 .MSTORE]

/-- The appended four-limb loop head (pc 10754): a byte copy of the eight-limb head. -/
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8558 2 2080,
   opAt 8559 .MLOAD,
   opAt 8560 (.Dup ⟨0, by decide⟩),
   opAt 8561 (.Dup ⟨14, by decide⟩),
   opAt 8562 .SHR,
   opAt 8563 (.Swap ⟨0, by decide⟩),
   pushAt 8564 2 1600,
   opAt 8565 .MLOAD,
   opAt 8566 .SHL,
   pushAt 8567 2 2112,
   opAt 8568 .MLOAD,
   opAt 8569 (.Dup ⟨15, by decide⟩),
   opAt 8570 .SHR,
   opAt 8571 .ADD,
   opAt 8572 (.Dup ⟨13, by decide⟩),
   opAt 8573 (.Dup ⟨0, by decide⟩),
   opAt 8574 (.Dup ⟨13, by decide⟩),
   opAt 8575 (.Dup ⟨4, by decide⟩),
   opAt 8576 .MULMOD,
   opAt 8577 (.Dup ⟨2, by decide⟩),
   opAt 8578 .ADDMOD,
   opAt 8579 (.Swap ⟨0, by decide⟩),
   opAt 8580 .SUB,
   opAt 8581 (.Dup ⟨12, by decide⟩),
   opAt 8582 .MUL,
   opAt 8583 (.Dup ⟨15, by decide⟩),
   opAt 8584 (.Dup ⟨1, by decide⟩),
   pushAt 8585 3 128,
   opAt 8586 .SHR,
   opAt 8587 .MUL,
   opAt 8588 (.Dup ⟨1, by decide⟩),
   pushAt 8589 0 0,
   opAt 8590 .MLOAD,
   opAt 8591 .MUL,
   pushAt 8592 2 2112,
   opAt 8593 .MLOAD,
   opAt 8594 .SUB,
   opAt 8595 .LT,
   opAt 8596 (.Swap ⟨0, by decide⟩),
   opAt 8597 .SUB,
   pushAt 8598 0 0,
   opAt 8599 .NOT,
   opAt 8600 (.Swap ⟨1, by decide⟩),
   opAt 8601 (.Dup ⟨14, by decide⟩),
   opAt 8602 .GT,
   opAt 8603 (.Dup ⟨2, by decide⟩),
   opAt 8604 .ADD,
   opAt 8605 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2362 2 2080,
   opAt 2363 .MLOAD,
   opAt 2364 (.Dup ⟨1, by decide⟩),
   opAt 2365 .ADD,
   opAt 2366 (.Dup ⟨0, by decide⟩),
   opAt 2367 (.Swap ⟨1, by decide⟩),
   opAt 2368 .GT,
   opAt 2369 (.Dup ⟨1, by decide⟩),
   opAt 2370 (.Dup ⟨3, by decide⟩),
   opAt 2371 .GT,
   opAt 2372 .GT,
   opAt 2373 (.Swap ⟨2, by decide⟩),
   opAt 2374 .POP,
   opAt 2375 .SUB,
   opAt 2376 (.Dup ⟨0, by decide⟩),
   pushAt 2377 2 2080,
   opAt 2378 .MSTORE,
   opAt 2379 (.Dup ⟨1, by decide⟩),
   opAt 2380 .OR,
   pushAt 2381 4 3104,
   opAt 2382 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2410 .JUMPDEST,
   opAt 2411 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2412 .JUMPDEST,
   pushAt 2413 0 0,
   pushAt 2414 2 2784,
   opAt 2415 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2416 .JUMPDEST,
   opAt 2417 (.Dup ⟨0, by decide⟩),
   opAt 2418 .MLOAD,
   pushAt 2419 2 2112,
   opAt 2420 (.Dup ⟨2, by decide⟩),
   opAt 2421 .SUB,
   opAt 2422 .MLOAD,
   opAt 2423 (.Dup ⟨1, by decide⟩),
   opAt 2424 .ADD,
   opAt 2425 (.Swap ⟨0, by decide⟩),
   opAt 2426 (.Dup ⟨1, by decide⟩),
   opAt 2427 .LT,
   opAt 2428 (.Swap ⟨0, by decide⟩),
   opAt 2429 (.Dup ⟨3, by decide⟩),
   opAt 2430 .ADD,
   opAt 2431 (.Swap ⟨2, by decide⟩),
   opAt 2432 (.Dup ⟨3, by decide⟩),
   opAt 2433 .LT,
   opAt 2434 .OR,
   opAt 2435 (.Swap ⟨1, by decide⟩),
   opAt 2436 (.Dup ⟨1, by decide⟩),
   opAt 2437 .MSTORE,
   pushAt 2438 1 31,
   opAt 2439 .NOT,
   opAt 2440 .ADD,
   pushAt 2441 2 2111,
   opAt 2442 (.Dup ⟨1, by decide⟩),
   opAt 2443 .GT,
   pushAt 2444 2 3112,
   opAt 2445 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2446 .POP,
   pushAt 2447 2 2080,
   opAt 2448 .MLOAD,
   opAt 2449 (.Dup ⟨1, by decide⟩),
   opAt 2450 .ADD,
   opAt 2451 (.Dup ⟨0, by decide⟩),
   pushAt 2452 2 2080,
   opAt 2453 .MSTORE,
   opAt 2454 .LT,
   opAt 2455 .ISZERO,
   pushAt 2456 2 3106,
   opAt 2457 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2458 2 2080,
   opAt 2459 .MLOAD,
   opAt 2460 (.Dup ⟨0, by decide⟩),
   opAt 2461 .ISZERO,
   pushAt 2462 2 3063,
   opAt 2463 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2383 .JUMPDEST,
   opAt 2384 .NOT,
   opAt 2385 .ADD,
   opAt 2386 (.Dup ⟨0, by decide⟩),
   opAt 2387 (.Dup ⟨2, by decide⟩),
   opAt 2388 .JUMPI]

/-- The loop exit after the last step: `SHIFT_DONE` is the `JUMPI` fall-through itself (the
exit block sits right behind the bottom test), so the exit path is empty. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- The four-limb private middle block (pc 10945). -/
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8708 2 2080,
   opAt 8709 .MLOAD,
   opAt 8710 (.Dup ⟨1, by decide⟩),
   opAt 8711 .ADD,
   opAt 8712 (.Dup ⟨0, by decide⟩),
   opAt 8713 (.Swap ⟨1, by decide⟩),
   opAt 8714 .GT,
   opAt 8715 (.Dup ⟨1, by decide⟩),
   opAt 8716 (.Dup ⟨3, by decide⟩),
   opAt 8717 .GT,
   opAt 8718 .GT,
   opAt 8719 (.Swap ⟨2, by decide⟩),
   opAt 8720 .POP,
   opAt 8721 .SUB,
   opAt 8722 (.Dup ⟨0, by decide⟩),
   pushAt 8723 2 2080,
   opAt 8724 .MSTORE,
   opAt 8725 (.Dup ⟨1, by decide⟩),
   opAt 8726 .OR,
   pushAt 8727 4 3104,
   opAt 8728 .JUMPI]

/-- The four-limb private counter (pc 10974; nothing jumps here, so no `JUMPDEST`). -/
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8729 .NOT,
   opAt 8730 .ADD,
   opAt 8731 (.Dup ⟨0, by decide⟩),
   opAt 8732 (.Dup ⟨2, by decide⟩),
   opAt 8733 .JUMPI]

/-- The four-limb loop exit: `PUSH2 3069 JUMP` (pc 10979) to the shared exit block. -/
def blkExit4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8734 2 3069,
   opAt 8735 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2390 = true :=
  CycleSubmission.Global.Binding.jumpDest 1873 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 219 = true :=
  CycleSubmission.Global.Binding.jumpDest 145 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2412 = true :=
  CycleSubmission.Global.Binding.jumpDest 1886 (by rfl)


theorem jumpDestNeg4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2336 = true :=
  CycleSubmission.Global.Binding.jumpDest 1843 (by rfl)

theorem jumpDestNegT :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2470 = true :=
  CycleSubmission.Global.Binding.jumpDest 1922 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2714 = true :=
  CycleSubmission.Global.Binding.jumpDest 2091 (by rfl)

/-- The appended four-limb loop head. -/
theorem jumpDestHead4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10754 = true :=
  CycleSubmission.Global.Binding.jumpDest 8550 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3106 = true :=
  CycleSubmission.Global.Binding.jumpDest 2412 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3112 = true :=
  CycleSubmission.Global.Binding.jumpDest 2416 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3104 = true :=
  CycleSubmission.Global.Binding.jumpDest 2410 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3063 = true :=
  CycleSubmission.Global.Binding.jumpDest 2383 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3069 = true :=
  CycleSubmission.Global.Binding.jumpDest 2389 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3944 = true :=
  CycleSubmission.Global.Binding.jumpDest 3052 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2329 = true :=
  CycleSubmission.Global.Binding.jumpDest 1839 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2946 + 116·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2057 (.Dup ⟨0, by decide⟩),
   pushAt 2058 1 29,
   opAt 2059 .MUL,
   pushAt 2060 2 3017,
   opAt 2061 .SUB,
   pushAt 2062 2 1698,
   opAt 2063 .MSTORE,
   pushAt 2064 1 32,
   opAt 2065 .MLOAD,
   pushAt 2066 1 128,
   opAt 2067 .SHR,
   opAt 2068 (.Swap ⟨12, by decide⟩),
   pushAt 2069 1 1,
   opAt 2070 .EQ,
   pushAt 2071 2 2656,
   opAt 2072 .MLOAD,
   opAt 2073 .CALLDATALOAD,
   pushAt 2074 0 0,
   opAt 2075 .BYTE,
   pushAt 2076 1 3,
   opAt 2077 .EQ,
   opAt 2078 .AND,
   opAt 2079 (.Dup ⟨0, by decide⟩),
   pushAt 2080 2 1760,
   opAt 2081 .MSTORE,
   opAt 2082 .SHR,
   opAt 2083 (.Dup ⟨13, by decide⟩),
   pushAt 2084 2 2010,
   opAt 2085 .MUL,
   pushAt 2086 2 18794,
   opAt 2087 .SUB,
   opAt 2088 (.Swap ⟨0, by decide⟩),
   opAt 2089 (.Dup ⟨1, by decide⟩),
   opAt 2090 .JUMP]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3380). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2389 .JUMPDEST,
   opAt 2390 .POP,
   pushAt 2391 2 1760,
   opAt 2392 .MLOAD,
   opAt 2393 .ISZERO,
   pushAt 2394 2 3944,
   opAt 2395 .JUMPI]

/-- The cleanup tail (pcs 3866-3887): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3052 .JUMPDEST,
   opAt 3053 .POP,
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
   pushAt 3069 2 2317,
   opAt 3070 .ADD,
   opAt 3071 .JUMP]

end CycleSubmission.Global.Fast
