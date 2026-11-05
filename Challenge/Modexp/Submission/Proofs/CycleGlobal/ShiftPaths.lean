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
  [opAt 1868 .JUMPDEST,
   opAt 1869 (.Dup ⟨0, by decide⟩),
   opAt 1870 (.Dup ⟨3, by decide⟩),
   opAt 1871 .XOR,
   pushAt 1872 2 219,
   opAt 1873 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1874 (.Dup ⟨0, by decide⟩),
   pushAt 1875 1 96,
   pushAt 1876 2 2112,
   opAt 1877 .CALLDATACOPY,
   pushAt 1878 2 2412,
   pushAt 1879 2 3493,
   opAt 1880 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1886 (.Dup ⟨0, by decide⟩),
   pushAt 1887 1 128,
   opAt 1888 .EQ,
   pushAt 1889 2 2336,
   opAt 1890 .JUMPI]

/-- Negation cell at pc 2429: `NEG[1504] := 0 - mem[224]`. -/
def negS8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1891 1 224,
   opAt 1892 .MLOAD,
   pushAt 1893 0 0,
   opAt 1894 .SUB,
   pushAt 1895 2 1504,
   opAt 1896 .MSTORE]

/-- Negation cell at pc 2438: `NEG[1472] := NOT mem[192]`. -/
def negN8a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1897 1 192,
   opAt 1898 .MLOAD,
   opAt 1899 .NOT,
   pushAt 1900 2 1472,
   opAt 1901 .MSTORE]

/-- Negation cell at pc 2446: `NEG[1440] := NOT mem[160]`. -/
def negN8b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1902 1 160,
   opAt 1903 .MLOAD,
   opAt 1904 .NOT,
   pushAt 1905 2 1440,
   opAt 1906 .MSTORE]

/-- Negation cell at pc 2454: `NEG[1408] := NOT mem[128]`. -/
def negN8c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1907 1 128,
   opAt 1908 .MLOAD,
   opAt 1909 .NOT,
   pushAt 1910 2 1408,
   opAt 1911 .MSTORE]

/-- Negation cell at pc 2462: `NEG[1376] := NOT mem[96]`. -/
def negN8d :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1912 1 96,
   opAt 1913 .MLOAD,
   opAt 1914 .NOT,
   pushAt 1915 2 1376,
   opAt 1916 .MSTORE]

/- Negation cell at pc 2471: `NEG[1344] := NOT mem[64]`. -/


/- Negation cell at pc 2479: `NEG[1312] := NOT mem[32]`. -/


/- Negation cell at pc 2487: `NEG[1280] := NOT mem[0]`. -/


/-- Negation cell at pc 2337: `NEG[1376] := 0 - mem[96]`. -/
def negS4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1839 1 96,
   opAt 1840 .MLOAD,
   pushAt 1841 0 0,
   opAt 1842 .SUB,
   pushAt 1843 2 1376,
   opAt 1844 .MSTORE]

/-- The four-limb stub's `JUMPDEST` (pc 2336). -/
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1838 .JUMPDEST]

/-- The four-limb stub joins `NEG_TAIL` (pc 2470). -/
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1845 2 2470,
   opAt 1846 .JUMP]

/-- `NEG_TAIL`'s `JUMPDEST` (pc 2470). -/
def negJT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1917 .JUMPDEST]

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
  [opAt 1917 .JUMPDEST,
   pushAt 1918 2 64,
   opAt 1919 .MLOAD,
   opAt 1920 .NOT,
   pushAt 1921 2 1344,
   opAt 1922 .MSTORE,
   pushAt 1923 1 32,
   opAt 1924 .MLOAD,
   opAt 1925 .NOT,
   pushAt 1926 2 1312,
   opAt 1927 .MSTORE,
   pushAt 1928 0 0,
   opAt 1929 .MLOAD,
   opAt 1930 (.Dup ⟨0, by decide⟩),
   opAt 1931 .NOT,
   pushAt 1932 2 1280,
   opAt 1933 .MSTORE]


/-- `blk2919`, first part: `L = d &&& -d` twice on top of `d`, stopping before the `CLZ`. -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1934 (.Dup ⟨0, by decide⟩),
   pushAt 1935 0 0,
   opAt 1936 .SUB,
   opAt 1937 (.Dup ⟨1, by decide⟩),
   opAt 1938 .AND,
   opAt 1939 (.Dup ⟨0, by decide⟩)]


/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1941 (.Dup ⟨0, by decide⟩),
   pushAt 1942 1 1,
   opAt 1943 .ADD,
   pushAt 1944 2 1600,
   opAt 1945 .MSTORE,
   pushAt 1946 1 255,
   opAt 1947 .SUB,
   pushAt 1948 3 1536,
   opAt 1949 .MSTORE,
   opAt 1950 (.Dup ⟨1, by decide⟩),
   opAt 1951 .DIV,
   opAt 1952 (.Dup ⟨0, by decide⟩),
   pushAt 1953 2 1568,
   opAt 1954 .MSTORE,
   opAt 1955 (.Dup ⟨0, by decide⟩),
   opAt 1956 (.Dup ⟨0, by decide⟩),
   pushAt 1957 0 0,
   opAt 1958 .SUB,
   opAt 1959 .MOD,
   pushAt 1960 2 1632,
   opAt 1961 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1962 2 2752,
   opAt 1963 .MLOAD,
   opAt 1964 .MLOAD,
   opAt 1965 (.Dup ⟨0, by decide⟩),
   opAt 1966 (.Dup ⟨2, by decide⟩),
   opAt 1967 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1968 (.Dup ⟨0, by decide⟩),
   pushAt 1969 1 3,
   opAt 1970 .MUL,
   pushAt 1971 1 2,
   opAt 1972 .XOR,
   opAt 1973 (.Dup ⟨0, by decide⟩),
   opAt 1974 (.Dup ⟨2, by decide⟩),
   opAt 1975 .MUL,
   pushAt 1976 1 2,
   opAt 1977 .SUB,
   opAt 1978 .MUL,
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
   opAt 2004 (.Swap ⟨1, by decide⟩),
   opAt 2005 .MUL,
   pushAt 2006 3 2,
   opAt 2007 .SUB,
   opAt 2008 .MUL]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2009 (.Dup ⟨0, by decide⟩),
   opAt 2010 (.Swap ⟨1, by decide⟩),
   opAt 2011 .MUL,
   pushAt 2012 4 1664,
   opAt 2013 .MSTORE,
   opAt 2014 .MUL,
   pushAt 2015 0 0,
   opAt 2016 .SUB,
   pushAt 2017 4 2720,
   opAt 2018 .MSTORE,
   opAt 2019 .POP,
   pushAt 2020 0 0,
   pushAt 2021 0 0,
   opAt 2022 (.Dup ⟨4, by decide⟩),
   opAt 2023 (.Dup ⟨4, by decide⟩),
   opAt 2024 (.Dup ⟨7, by decide⟩),
   pushAt 2025 2 1536,
   opAt 2026 .MLOAD,
   pushAt 2027 2 1568,
   opAt 2028 .MLOAD,
   pushAt 2029 2 1664,
   opAt 2030 .MLOAD,
   pushAt 2031 2 1632,
   opAt 2032 .MLOAD,
   pushAt 2033 2 1504,
   opAt 2034 .MLOAD,
   pushAt 2035 2 1472,
   opAt 2036 .MLOAD,
   pushAt 2037 2 1440,
   opAt 2038 .MLOAD,
   pushAt 2039 2 1408,
   opAt 2040 .MLOAD,
   pushAt 2041 2 1376,
   opAt 2042 .MLOAD,
   pushAt 2043 2 1344,
   opAt 2044 .MLOAD,
   pushAt 2045 2 1312,
   opAt 2046 .MLOAD,
   opAt 2047 (.Dup ⟨12, by decide⟩)]


/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2075 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2076 (.Dup ⟨15, by decide⟩),
   pushAt 2077 2 2112,
   pushAt 2078 2 2080,
   opAt 2079 .MCOPY]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2080 2 2080,
   opAt 2081 .MLOAD,
   opAt 2082 (.Dup ⟨0, by decide⟩),
   opAt 2083 (.Dup ⟨14, by decide⟩),
   opAt 2084 .SHR,
   opAt 2085 (.Swap ⟨0, by decide⟩),
   pushAt 2086 2 1600,
   opAt 2087 .MLOAD,
   opAt 2088 .SHL,
   pushAt 2089 2 2112,
   opAt 2090 .MLOAD,
   opAt 2091 (.Dup ⟨15, by decide⟩),
   opAt 2092 .SHR,
   opAt 2093 .ADD,
   opAt 2094 (.Dup ⟨13, by decide⟩),
   opAt 2095 (.Dup ⟨0, by decide⟩),
   opAt 2096 (.Dup ⟨13, by decide⟩),
   opAt 2097 (.Dup ⟨4, by decide⟩),
   opAt 2098 .MULMOD,
   opAt 2099 (.Dup ⟨2, by decide⟩),
   opAt 2100 .ADDMOD,
   opAt 2101 (.Swap ⟨0, by decide⟩),
   opAt 2102 .SUB,
   opAt 2103 (.Dup ⟨12, by decide⟩),
   opAt 2104 .MUL,
   opAt 2105 (.Dup ⟨15, by decide⟩),
   opAt 2106 (.Dup ⟨1, by decide⟩),
   pushAt 2107 1 128,
   opAt 2108 .SHR,
   opAt 2109 .MUL,
   opAt 2110 (.Dup ⟨1, by decide⟩),
   pushAt 2111 0 0,
   opAt 2112 .MLOAD,
   opAt 2113 .MUL,
   pushAt 2114 2 2112,
   opAt 2115 .MLOAD,
   opAt 2116 .SUB,
   opAt 2117 .LT,
   opAt 2118 (.Swap ⟨0, by decide⟩),
   opAt 2119 .SUB,
   pushAt 2120 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2121 (.Swap ⟨1, by decide⟩),
   opAt 2122 (.Dup ⟨14, by decide⟩),
   opAt 2123 .GT,
   opAt 2124 (.Dup ⟨2, by decide⟩),
   opAt 2125 .ADD,
   opAt 2126 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8337 .JUMPDEST]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8338 (.Dup ⟨15, by decide⟩),
   pushAt 8339 2 2112,
   pushAt 8340 2 2080,
   opAt 8341 .MCOPY]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8342 2 2080,
   opAt 8343 .MLOAD,
   opAt 8344 (.Dup ⟨0, by decide⟩),
   opAt 8345 (.Dup ⟨14, by decide⟩),
   opAt 8346 .SHR,
   opAt 8347 (.Swap ⟨0, by decide⟩),
   pushAt 8348 2 1600,
   opAt 8349 .MLOAD,
   opAt 8350 .SHL,
   pushAt 8351 2 2112,
   opAt 8352 .MLOAD,
   opAt 8353 (.Dup ⟨15, by decide⟩),
   opAt 8354 .SHR,
   opAt 8355 .ADD,
   opAt 8356 (.Dup ⟨13, by decide⟩),
   opAt 8357 (.Dup ⟨0, by decide⟩),
   opAt 8358 (.Dup ⟨13, by decide⟩),
   opAt 8359 (.Dup ⟨4, by decide⟩),
   opAt 8360 .MULMOD,
   opAt 8361 (.Dup ⟨2, by decide⟩),
   opAt 8362 .ADDMOD,
   opAt 8363 (.Swap ⟨0, by decide⟩),
   opAt 8364 .SUB,
   opAt 8365 (.Dup ⟨12, by decide⟩),
   opAt 8366 .MUL,
   opAt 8367 (.Dup ⟨15, by decide⟩),
   opAt 8368 (.Dup ⟨1, by decide⟩),
   pushAt 8369 1 128,
   opAt 8370 .SHR,
   opAt 8371 .MUL,
   opAt 8372 (.Dup ⟨1, by decide⟩),
   pushAt 8373 0 0,
   opAt 8374 .MLOAD,
   opAt 8375 .MUL,
   pushAt 8376 2 2112,
   opAt 8377 .MLOAD,
   opAt 8378 .SUB,
   opAt 8379 .LT,
   opAt 8380 (.Swap ⟨0, by decide⟩),
   opAt 8381 .SUB,
   pushAt 8382 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8383 (.Swap ⟨1, by decide⟩),
   opAt 8384 (.Dup ⟨14, by decide⟩),
   opAt 8385 .GT,
   opAt 8386 (.Dup ⟨2, by decide⟩),
   opAt 8387 .ADD,
   opAt 8388 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2341 2 2080,
   opAt 2342 .MLOAD,
   opAt 2343 (.Dup ⟨1, by decide⟩),
   opAt 2344 .ADD,
   opAt 2345 (.Dup ⟨0, by decide⟩),
   opAt 2346 (.Swap ⟨1, by decide⟩),
   opAt 2347 .GT,
   opAt 2348 (.Dup ⟨1, by decide⟩),
   opAt 2349 (.Dup ⟨3, by decide⟩),
   opAt 2350 .GT,
   opAt 2351 .GT,
   opAt 2352 (.Swap ⟨2, by decide⟩),
   opAt 2353 .POP,
   opAt 2354 .SUB,
   opAt 2355 (.Dup ⟨0, by decide⟩),
   pushAt 2356 2 2080,
   opAt 2357 .MSTORE,
   opAt 2358 (.Dup ⟨1, by decide⟩),
   opAt 2359 .OR,
   pushAt 2360 2 3125,
   opAt 2361 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2390 .JUMPDEST,
   opAt 2391 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2392 .JUMPDEST,
   pushAt 2393 0 0,
   pushAt 2394 2 2784,
   opAt 2395 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2396 .JUMPDEST,
   opAt 2397 (.Dup ⟨0, by decide⟩),
   opAt 2398 .MLOAD,
   pushAt 2399 2 2112,
   opAt 2400 (.Dup ⟨2, by decide⟩),
   opAt 2401 .SUB,
   opAt 2402 .MLOAD,
   opAt 2403 (.Dup ⟨1, by decide⟩),
   opAt 2404 .ADD,
   opAt 2405 (.Swap ⟨0, by decide⟩),
   opAt 2406 (.Dup ⟨1, by decide⟩),
   opAt 2407 .LT,
   opAt 2408 (.Swap ⟨0, by decide⟩),
   opAt 2409 (.Dup ⟨3, by decide⟩),
   opAt 2410 .ADD,
   opAt 2411 (.Swap ⟨2, by decide⟩),
   opAt 2412 (.Dup ⟨3, by decide⟩),
   opAt 2413 .LT,
   opAt 2414 .OR,
   opAt 2415 (.Swap ⟨1, by decide⟩),
   opAt 2416 (.Dup ⟨1, by decide⟩),
   opAt 2417 .MSTORE,
   pushAt 2418 1 31,
   opAt 2419 .NOT,
   opAt 2420 .ADD,
   pushAt 2421 2 2111,
   opAt 2422 (.Dup ⟨1, by decide⟩),
   opAt 2423 .GT,
   pushAt 2424 2 3133,
   opAt 2425 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2426 .POP,
   pushAt 2427 2 2080,
   opAt 2428 .MLOAD,
   opAt 2429 (.Dup ⟨1, by decide⟩),
   opAt 2430 .ADD,
   opAt 2431 (.Dup ⟨0, by decide⟩),
   pushAt 2432 2 2080,
   opAt 2433 .MSTORE,
   opAt 2434 .LT,
   opAt 2435 .ISZERO,
   pushAt 2436 2 3127,
   opAt 2437 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2438 2 2080,
   opAt 2439 .MLOAD,
   opAt 2440 (.Dup ⟨0, by decide⟩),
   opAt 2441 .ISZERO,
   pushAt 2442 2 3085,
   opAt 2443 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2362 .JUMPDEST,
   opAt 2363 .NOT,
   opAt 2364 .ADD,
   opAt 2365 (.Dup ⟨0, by decide⟩),
   opAt 2366 (.Dup ⟨2, by decide⟩),
   opAt 2367 .JUMPI]

/-- The loop exit after the last step: `SHIFT_DONE` is the `JUMPI` fall-through itself (the
exit block sits right behind the bottom test), so the exit path is empty. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- The four-limb private middle block (pc 10941). -/
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8491 2 2080,
   opAt 8492 .MLOAD,
   opAt 8493 (.Dup ⟨1, by decide⟩),
   opAt 8494 .ADD,
   opAt 8495 (.Dup ⟨0, by decide⟩),
   opAt 8496 (.Swap ⟨1, by decide⟩),
   opAt 8497 .GT,
   opAt 8498 (.Dup ⟨1, by decide⟩),
   opAt 8499 (.Dup ⟨3, by decide⟩),
   opAt 8500 .GT,
   opAt 8501 .GT,
   opAt 8502 (.Swap ⟨2, by decide⟩),
   opAt 8503 .POP,
   opAt 8504 .SUB,
   opAt 8505 (.Dup ⟨0, by decide⟩),
   pushAt 8506 2 2080,
   opAt 8507 .MSTORE,
   opAt 8508 (.Dup ⟨1, by decide⟩),
   opAt 8509 .OR,
   pushAt 8510 4 3125,
   opAt 8511 .JUMPI]

/-- The four-limb private counter (pc 10970; nothing jumps here, so no `JUMPDEST`). -/
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8512 .NOT,
   opAt 8513 .ADD,
   opAt 8514 (.Dup ⟨0, by decide⟩),
   opAt 8515 (.Dup ⟨2, by decide⟩),
   opAt 8516 .JUMPI]

/-- The four-limb loop exit: `PUSH2 3069 JUMP` (pc 10975) to the shared exit block. -/
def blkExit4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8517 2 3091,
   opAt 8518 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2390 = true :=
  CycleSubmission.Global.Binding.jumpDest 1868 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 219 = true :=
  CycleSubmission.Global.Binding.jumpDest 143 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2412 = true :=
  CycleSubmission.Global.Binding.jumpDest 1881 (by rfl)


theorem jumpDestNeg4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2336 = true :=
  CycleSubmission.Global.Binding.jumpDest 1838 (by rfl)

theorem jumpDestNegT :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2470 = true :=
  CycleSubmission.Global.Binding.jumpDest 1917 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2714 = true :=
  CycleSubmission.Global.Binding.jumpDest 2075 (by rfl)

/-- The appended four-limb loop head. -/
theorem jumpDestHead4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10726 = true :=
  CycleSubmission.Global.Binding.jumpDest 8337 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3127 = true :=
  CycleSubmission.Global.Binding.jumpDest 2392 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3133 = true :=
  CycleSubmission.Global.Binding.jumpDest 2396 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3125 = true :=
  CycleSubmission.Global.Binding.jumpDest 2390 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3085 = true :=
  CycleSubmission.Global.Binding.jumpDest 2362 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3091 = true :=
  CycleSubmission.Global.Binding.jumpDest 2368 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3944 = true :=
  CycleSubmission.Global.Binding.jumpDest 3025 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2329 = true :=
  CycleSubmission.Global.Binding.jumpDest 1834 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2946 + 116·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2048 13 32,
   opAt 2049 .MLOAD,
   pushAt 2050 1 128,
   opAt 2051 .SHR,
   opAt 2052 (.Swap ⟨12, by decide⟩),
   pushAt 2053 1 1,
   opAt 2054 .EQ,
   pushAt 2055 2 2656,
   opAt 2056 .MLOAD,
   opAt 2057 .CALLDATALOAD,
   pushAt 2058 0 0,
   opAt 2059 .BYTE,
   pushAt 2060 1 3,
   opAt 2061 .EQ,
   opAt 2062 .AND,
   opAt 2063 (.Dup ⟨0, by decide⟩),
   pushAt 2064 2 1760,
   opAt 2065 .MSTORE,
   opAt 2066 .SHR,
   opAt 2067 (.Dup ⟨13, by decide⟩),
   pushAt 2068 2 2003,
   opAt 2069 .MUL,
   pushAt 2070 2 18738,
   opAt 2071 .SUB,
   opAt 2072 (.Swap ⟨0, by decide⟩),
   opAt 2073 (.Dup ⟨1, by decide⟩),
   opAt 2074 .JUMP]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3380). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2368 .JUMPDEST,
   opAt 2369 .POP,
   pushAt 2370 2 1760,
   opAt 2371 .MLOAD,
   opAt 2372 .ISZERO,
   pushAt 2373 2 3944,
   opAt 2374 .JUMPI]

/-- The cleanup tail (pcs 3866-3887): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3025 .JUMPDEST,
   opAt 3026 .POP,
   opAt 3027 .POP,
   opAt 3028 .POP,
   opAt 3029 .POP,
   opAt 3030 .POP,
   opAt 3031 .POP,
   opAt 3032 .POP,
   opAt 3033 .POP,
   opAt 3034 .POP,
   opAt 3035 .POP,
   opAt 3036 .POP,
   opAt 3037 .POP,
   opAt 3038 .POP,
   opAt 3039 .POP,
   opAt 3040 .POP,
   opAt 3041 .POP,
   pushAt 3042 2 2317,
   opAt 3043 .ADD,
   opAt 3044 .JUMP]

end CycleSubmission.Global.Fast
