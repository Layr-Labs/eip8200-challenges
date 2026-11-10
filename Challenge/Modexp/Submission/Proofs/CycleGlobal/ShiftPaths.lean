import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs

noncomputable section
set_option warningAsError true
set_option maxRecDepth 100000
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
  [opAt 1855 .JUMPDEST,
   opAt 1856 (.Dup dA0),
   opAt 1857 (.Dup dA3),
   opAt 1858 .XOR,
   pushAt 1859 1 207,
   opAt 1860 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1861 (.Dup dA0),
   pushAt 1862 1 96,
   pushAt 1863 2 2112,
   opAt 1864 .CALLDATACOPY,
   pushAt 1865 2 2378,
   pushAt 1866 2 3484,
   opAt 1867 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1873 (.Dup dA0),
   pushAt 1874 1 128,
   opAt 1875 .EQ,
   pushAt 1876 2 2303,
   opAt 1877 .JUMPI]

/-- Negation cell at pc 2429: `NEG[1504] := 0 - mem[224]`. -/
def negS8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1878 1 224,
   opAt 1879 .MLOAD,
   pushAt 1880 0 0,
   opAt 1881 .SUB,
   pushAt 1882 2 1504,
   opAt 1883 .MSTORE]

/-- Negation cell at pc 2438: `NEG[1472] := NOT mem[192]`. -/
def negN8a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1884 1 192,
   opAt 1885 .MLOAD,
   opAt 1886 .NOT,
   pushAt 1887 2 1472,
   opAt 1888 .MSTORE]

/-- Negation cell at pc 2446: `NEG[1440] := NOT mem[160]`. -/
def negN8b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1889 1 160,
   opAt 1890 .MLOAD,
   opAt 1891 .NOT,
   pushAt 1892 2 1440,
   opAt 1893 .MSTORE]

/-- Negation cell at pc 2454: `NEG[1408] := NOT mem[128]`. -/
def negN8c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1894 1 128,
   opAt 1895 .MLOAD,
   opAt 1896 .NOT,
   pushAt 1897 2 1408,
   opAt 1898 .MSTORE]

/-- Negation cell at pc 2462: `NEG[1376] := NOT mem[96]`. -/
def negN8d :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1899 1 96,
   opAt 1900 .MLOAD,
   opAt 1901 .NOT,
   pushAt 1902 2 1376,
   opAt 1903 .MSTORE]

/- Negation cell at pc 2471: `NEG[1344] := NOT mem[64]`. -/


/- Negation cell at pc 2479: `NEG[1312] := NOT mem[32]`. -/


/- Negation cell at pc 2487: `NEG[1280] := NOT mem[0]`. -/


/-- Negation cell at pc 2337: `NEG[1376] := 0 - mem[96]`. -/
def negS4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1826 1 96,
   opAt 1827 .MLOAD,
   pushAt 1828 0 0,
   opAt 1829 .SUB,
   pushAt 1830 2 1376,
   opAt 1831 .MSTORE]

/-- The four-limb stub's `JUMPDEST` (pc 2336). -/
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1825 .JUMPDEST]

/-- The four-limb stub joins `NEG_TAIL` (pc 2470). -/
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1832 2 2436,
   opAt 1833 .JUMP]

/-- `NEG_TAIL`'s `JUMPDEST` (pc 2470). -/
def negJT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1904 .JUMPDEST]

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
  [opAt 1904 .JUMPDEST,
   pushAt 1905 1 64,
   opAt 1906 .MLOAD,
   opAt 1907 .NOT,
   pushAt 1908 2 1344,
   opAt 1909 .MSTORE,
   pushAt 1910 1 32,
   opAt 1911 .MLOAD,
   opAt 1912 .NOT,
   pushAt 1913 2 1312,
   opAt 1914 .MSTORE,
   pushAt 1915 0 0,
   opAt 1916 .MLOAD,
   opAt 1917 (.Dup dA0),
   opAt 1918 .NOT,
   pushAt 1919 2 1280,
   opAt 1920 .MSTORE]


/-- `blk2919`, first part: `L = d &&& -d` twice on top of `d`, stopping before the `CLZ`. -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1921 (.Dup dA0),
   pushAt 1922 0 0,
   opAt 1923 .SUB,
   opAt 1924 (.Dup dA1),
   opAt 1925 .AND,
   opAt 1926 (.Dup dA0)]


/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1928 (.Dup dA0),
   pushAt 1929 1 1,
   opAt 1930 .ADD,
   pushAt 1931 2 1600,
   opAt 1932 .MSTORE,
   pushAt 1933 1 255,
   opAt 1934 .SUB,
   pushAt 1935 2 1536,
   opAt 1936 .MSTORE,
   opAt 1937 (.Dup dA1),
   opAt 1938 .DIV,
   opAt 1939 (.Dup dA0),
   pushAt 1940 2 1568,
   opAt 1941 .MSTORE,
   opAt 1942 (.Dup dA0),
   opAt 1943 (.Dup dA0),
   pushAt 1944 0 0,
   opAt 1945 .SUB,
   opAt 1946 .MOD,
   pushAt 1947 2 1632,
   opAt 1948 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1949 2 2752,
   opAt 1950 .MLOAD,
   opAt 1951 .MLOAD,
   opAt 1952 (.Dup dA0),
   opAt 1953 (.Dup dA2),
   opAt 1954 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1955 (.Dup dA0),
   pushAt 1956 1 3,
   opAt 1957 .MUL,
   pushAt 1958 1 2,
   opAt 1959 .XOR,
   opAt 1960 (.Dup dA0),
   opAt 1961 (.Dup dA2),
   opAt 1962 .MUL,
   pushAt 1963 1 2,
   opAt 1964 .SUB,
   opAt 1965 .MUL,
   opAt 1966 (.Dup dA0),
   opAt 1967 (.Dup dA2),
   opAt 1968 .MUL,
   pushAt 1969 1 2,
   opAt 1970 .SUB,
   opAt 1971 .MUL,
   opAt 1972 (.Dup dA0),
   opAt 1973 (.Dup dA2),
   opAt 1974 .MUL,
   pushAt 1975 1 2,
   opAt 1976 .SUB,
   opAt 1977 .MUL,
   opAt 1978 (.Dup dA0),
   opAt 1979 (.Dup dA2),
   opAt 1980 .MUL,
   pushAt 1981 1 2,
   opAt 1982 .SUB,
   opAt 1983 .MUL,
   opAt 1984 (.Dup dA0),
   opAt 1985 (.Dup dA2),
   opAt 1986 .MUL,
   pushAt 1987 1 2,
   opAt 1988 .SUB,
   opAt 1989 .MUL,
   opAt 1990 (.Dup dA0),
   opAt 1991 (.Swap sA1),
   opAt 1992 .MUL,
   pushAt 1993 1 2,
   opAt 1994 .SUB,
   opAt 1995 .MUL]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1996 (.Dup dA0),
   opAt 1997 (.Swap sA1),
   opAt 1998 .MUL,
   pushAt 1999 2 1664,
   opAt 2000 .MSTORE,
   opAt 2001 .MUL,
   pushAt 2002 0 0,
   opAt 2003 .SUB,
   pushAt 2004 2 2720,
   opAt 2005 .MSTORE,
   opAt 2006 .POP,
   pushAt 2007 0 0,
   pushAt 2008 0 0,
   opAt 2009 (.Dup dA4),
   opAt 2010 (.Dup dA4),
   opAt 2011 (.Dup dA7),
   pushAt 2012 2 1536,
   opAt 2013 .MLOAD,
   pushAt 2014 2 1568,
   opAt 2015 .MLOAD,
   pushAt 2016 2 1664,
   opAt 2017 .MLOAD,
   pushAt 2018 2 1632,
   opAt 2019 .MLOAD,
   pushAt 2020 2 1504,
   opAt 2021 .MLOAD,
   pushAt 2022 2 1472,
   opAt 2023 .MLOAD,
   pushAt 2024 2 1440,
   opAt 2025 .MLOAD,
   pushAt 2026 2 1408,
   opAt 2027 .MLOAD,
   pushAt 2028 2 1376,
   opAt 2029 .MLOAD,
   pushAt 2030 2 1344,
   opAt 2031 .MLOAD,
   pushAt 2032 2 1312,
   opAt 2033 .MLOAD,
   opAt 2034 (.Dup dA12)]


/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2062 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2063 (.Dup dA15),
   pushAt 2064 2 2112,
   pushAt 2065 2 2080,
   opAt 2066 .MCOPY]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2067 2 2080,
   opAt 2068 .MLOAD,
   opAt 2069 (.Dup dA0),
   opAt 2070 (.Dup dA14),
   opAt 2071 .SHR,
   opAt 2072 (.Swap sA0),
   pushAt 2073 2 1600,
   opAt 2074 .MLOAD,
   opAt 2075 .SHL,
   pushAt 2076 2 2112,
   opAt 2077 .MLOAD,
   opAt 2078 (.Dup dA15),
   opAt 2079 .SHR,
   opAt 2080 .ADD,
   opAt 2081 (.Dup dA13),
   opAt 2082 (.Dup dA0),
   opAt 2083 (.Dup dA13),
   opAt 2084 (.Dup dA4),
   opAt 2085 .MULMOD,
   opAt 2086 (.Dup dA2),
   opAt 2087 .ADDMOD,
   opAt 2088 (.Swap sA0),
   opAt 2089 .SUB,
   opAt 2090 (.Dup dA12),
   opAt 2091 .MUL,
   opAt 2092 (.Dup dA15),
   opAt 2093 (.Dup dA1),
   pushAt 2094 1 128,
   opAt 2095 .SHR,
   opAt 2096 .MUL,
   opAt 2097 (.Dup dA1),
   pushAt 2098 0 0,
   opAt 2099 .MLOAD,
   opAt 2100 .MUL,
   pushAt 2101 2 2112,
   opAt 2102 .MLOAD,
   opAt 2103 .SUB,
   opAt 2104 .LT,
   opAt 2105 (.Swap sA0),
   opAt 2106 .SUB,
   pushAt 2107 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2108 (.Swap sA1),
   opAt 2109 (.Dup dA14),
   opAt 2110 .GT,
   opAt 2111 (.Dup dA2),
   opAt 2112 .ADD,
   opAt 2113 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8243 .JUMPDEST]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8244 (.Dup dA15),
   pushAt 8245 2 2112,
   pushAt 8246 2 2080,
   opAt 8247 .MCOPY]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8248 2 2080,
   opAt 8249 .MLOAD,
   opAt 8250 (.Dup dA0),
   opAt 8251 (.Dup dA14),
   opAt 8252 .SHR,
   opAt 8253 (.Swap sA0),
   pushAt 8254 2 1600,
   opAt 8255 .MLOAD,
   opAt 8256 .SHL,
   pushAt 8257 2 2112,
   opAt 8258 .MLOAD,
   opAt 8259 (.Dup dA15),
   opAt 8260 .SHR,
   opAt 8261 .ADD,
   opAt 8262 (.Dup dA13),
   opAt 8263 (.Dup dA0),
   opAt 8264 (.Dup dA13),
   opAt 8265 (.Dup dA4),
   opAt 8266 .MULMOD,
   opAt 8267 (.Dup dA2),
   opAt 8268 .ADDMOD,
   opAt 8269 (.Swap sA0),
   opAt 8270 .SUB,
   opAt 8271 (.Dup dA12),
   opAt 8272 .MUL,
   opAt 8273 (.Dup dA15),
   opAt 8274 (.Dup dA1),
   pushAt 8275 1 128,
   opAt 8276 .SHR,
   opAt 8277 .MUL,
   opAt 8278 (.Dup dA1),
   pushAt 8279 0 0,
   opAt 8280 .MLOAD,
   opAt 8281 .MUL,
   pushAt 8282 2 2112,
   opAt 8283 .MLOAD,
   opAt 8284 .SUB,
   opAt 8285 .LT,
   opAt 8286 (.Swap sA0),
   opAt 8287 .SUB,
   pushAt 8288 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8289 (.Swap sA1),
   opAt 8290 (.Dup dA14),
   opAt 8291 .GT,
   opAt 8292 (.Dup dA2),
   opAt 8293 .ADD,
   opAt 8294 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  -- the three pops that discarded the old pointer loop's carried words are gone; the block now
  -- starts at the fall-through after the eight straight blocks
  [pushAt 2328 2 2080,
   opAt 2329 .MLOAD,
   opAt 2330 (.Dup dA1),
   opAt 2331 .ADD,
   opAt 2332 (.Dup dA0),
   opAt 2333 (.Swap sA1),
   opAt 2334 .GT,
   opAt 2335 (.Dup dA1),
   opAt 2336 (.Dup dA3),
   opAt 2337 .GT,
   opAt 2338 .GT,
   opAt 2339 (.Swap sA2),
   opAt 2340 .POP,
   opAt 2341 .SUB,
   opAt 2342 (.Dup dA0),
   pushAt 2343 2 2080,
   opAt 2344 .MSTORE,
   opAt 2345 .JUMPDEST,
   opAt 2346 .JUMPDEST,
   pushAt 2347 2 3069,
   opAt 2348 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2376 .JUMPDEST,
   opAt 2377 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2378 .JUMPDEST,
   pushAt 2379 0 0,
   pushAt 2380 2 2784,
   opAt 2381 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2382 .JUMPDEST,
   opAt 2383 (.Dup dA0),
   opAt 2384 .MLOAD,
   pushAt 2385 2 2112,
   opAt 2386 (.Dup dA2),
   opAt 2387 .SUB,
   opAt 2388 .MLOAD,
   opAt 2389 (.Dup dA1),
   opAt 2390 .ADD,
   opAt 2391 (.Swap sA0),
   opAt 2392 (.Dup dA1),
   opAt 2393 .LT,
   opAt 2394 (.Swap sA0),
   opAt 2395 (.Dup dA3),
   opAt 2396 .ADD,
   opAt 2397 (.Swap sA2),
   opAt 2398 (.Dup dA3),
   opAt 2399 .LT,
   opAt 2400 .OR,
   opAt 2401 (.Swap sA1),
   opAt 2402 (.Dup dA1),
   opAt 2403 .MSTORE,
   pushAt 2404 1 31,
   opAt 2405 .NOT,
   opAt 2406 .ADD,
   pushAt 2407 2 2111,
   opAt 2408 (.Dup dA1),
   opAt 2409 .GT,
   pushAt 2410 2 3077,
   opAt 2411 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2412 .POP,
   pushAt 2413 2 2080,
   opAt 2414 .MLOAD,
   opAt 2415 (.Dup dA1),
   opAt 2416 .ADD,
   opAt 2417 (.Dup dA0),
   pushAt 2418 2 2080,
   opAt 2419 .MSTORE,
   opAt 2420 .LT,
   opAt 2421 .ISZERO,
   pushAt 2422 2 3071,
   opAt 2423 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2424 2 2080,
   opAt 2425 .MLOAD,
   opAt 2426 (.Dup dA0),
   opAt 2427 .ISZERO,
   pushAt 2428 2 3030,
   opAt 2429 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2349 .JUMPDEST,
   opAt 2350 .NOT,
   opAt 2351 .ADD,
   opAt 2352 (.Dup dA0),
   opAt 2353 (.Dup dA2),
   opAt 2354 .JUMPI]

/-- The loop exit after the last step: `SHIFT_DONE` is the `JUMPI` fall-through itself (the
exit block sits right behind the bottom test), so the exit path is empty. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- The four-limb private middle block (pc 10941). -/
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8397 2 2080,
   opAt 8398 .MLOAD,
   opAt 8399 (.Dup dA1),
   opAt 8400 .ADD,
   opAt 8401 (.Dup dA0),
   opAt 8402 (.Swap sA1),
   opAt 8403 .GT,
   opAt 8404 (.Dup dA1),
   opAt 8405 (.Dup dA3),
   opAt 8406 .GT,
   opAt 8407 .GT,
   opAt 8408 (.Swap sA2),
   opAt 8409 .POP,
   opAt 8410 .SUB,
   opAt 8411 (.Dup dA0),
   pushAt 8412 2 2080,
   opAt 8413 .MSTORE,
   opAt 8414 .JUMPDEST,
   opAt 8415 .JUMPDEST,
   pushAt 8416 2 3069,
   opAt 8417 .JUMPI]

/-- The four-limb private counter (pc 10970; nothing jumps here, so no `JUMPDEST`). -/
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8418 .NOT,
   opAt 8419 .ADD,
   opAt 8420 (.Dup dA0),
   opAt 8421 (.Dup dA2),
   opAt 8422 .JUMPI]

/-- The four-limb loop exit: `PUSH2 3069 JUMP` (pc 10975) to the shared exit block. -/
def blkExit4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8423 2 3036,
   opAt 8424 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2357 = true :=
  CycleSubmission.Global.Binding.jumpDest 1855 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 135 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2378 = true :=
  CycleSubmission.Global.Binding.jumpDest 1868 (by rfl)


theorem jumpDestNeg4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2303 = true :=
  CycleSubmission.Global.Binding.jumpDest 1825 (by rfl)

theorem jumpDestNegT :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2436 = true :=
  CycleSubmission.Global.Binding.jumpDest 1904 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2660 = true :=
  CycleSubmission.Global.Binding.jumpDest 2062 (by rfl)

/-- The appended four-limb loop head. -/
theorem jumpDestHead4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10692 = true :=
  CycleSubmission.Global.Binding.jumpDest 8243 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3071 = true :=
  CycleSubmission.Global.Binding.jumpDest 2378 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3077 = true :=
  CycleSubmission.Global.Binding.jumpDest 2382 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3069 = true :=
  CycleSubmission.Global.Binding.jumpDest 2376 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3030 = true :=
  CycleSubmission.Global.Binding.jumpDest 2349 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3036 = true :=
  CycleSubmission.Global.Binding.jumpDest 2355 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3914 = true :=
  CycleSubmission.Global.Binding.jumpDest 3000 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2296 = true :=
  CycleSubmission.Global.Binding.jumpDest 1821 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2946 + 116·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2035 1 32,
   opAt 2036 .MLOAD,
   pushAt 2037 1 128,
   opAt 2038 .SHR,
   opAt 2039 (.Swap sA12),
   pushAt 2040 1 1,
   opAt 2041 .EQ,
   pushAt 2042 2 2656,
   opAt 2043 .MLOAD,
   opAt 2044 .CALLDATALOAD,
   pushAt 2045 0 0,
   opAt 2046 .BYTE,
   pushAt 2047 1 3,
   opAt 2048 .EQ,
   opAt 2049 .AND,
   opAt 2050 (.Dup dA0),
   pushAt 2051 2 1760,
   opAt 2052 .MSTORE,
   opAt 2053 .SHR,
   opAt 2054 (.Dup dA13),
   pushAt 2055 2 2008,
   opAt 2056 .MUL,
   pushAt 2057 2 18724,
   opAt 2058 .SUB,
   opAt 2059 (.Swap sA0),
   opAt 2060 (.Dup dA1),
   opAt 2061 .JUMP]

/-- The loop-exit check (pcs 3346-3356): drop the spent counter, and with the
squaring flag clear jump to the cleanup tail; otherwise fall into the squaring
round (pcs 3357-3380). -/
def blk3346 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2355 .JUMPDEST,
   opAt 2356 .POP,
   pushAt 2357 2 1760,
   opAt 2358 .MLOAD,
   opAt 2359 .ISZERO,
   pushAt 2360 2 3914,
   opAt 2361 .JUMPI]

/-- The cleanup tail (pcs 3866-3887): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3000 .JUMPDEST,
   opAt 3001 .POP,
   opAt 3002 .POP,
   opAt 3003 .POP,
   opAt 3004 .POP,
   opAt 3005 .POP,
   opAt 3006 .POP,
   opAt 3007 .POP,
   opAt 3008 .POP,
   opAt 3009 .POP,
   opAt 3010 .POP,
   opAt 3011 .POP,
   opAt 3012 .POP,
   opAt 3013 .POP,
   opAt 3014 .POP,
   opAt 3015 .POP,
   opAt 3016 .POP,
   pushAt 3017 2 2284,
   opAt 3018 .ADD,
   opAt 3019 .JUMP]

end CycleSubmission.Global.Fast
