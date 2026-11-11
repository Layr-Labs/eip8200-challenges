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
  [opAt 1868 .JUMPDEST,
   opAt 1869 (.Dup dA0),
   opAt 1870 (.Dup dA3),
   opAt 1871 .XOR,
   pushAt 1872 1 207,
   opAt 1873 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1874 (.Dup dA0),
   pushAt 1875 1 96,
   pushAt 1876 2 2112,
   opAt 1877 .CALLDATACOPY,
   pushAt 1878 2 2378,
   pushAt 1879 2 3484,
   opAt 1880 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1886 (.Dup dA0),
   pushAt 1887 1 128,
   opAt 1888 .EQ,
   pushAt 1889 2 2284,
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
  [pushAt 1814 1 96,
   opAt 1815 .MLOAD,
   pushAt 1816 0 0,
   opAt 1817 .SUB,
   pushAt 1818 2 1376,
   opAt 1819 .MSTORE]

/-- The four-limb stub's `JUMPDEST` (pc 2336). -/
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1813 .JUMPDEST]

/-- The four-limb stub joins `NEG_TAIL` (pc 2470). -/
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1820 2 2436,
   opAt 1821 .JUMP]

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
   pushAt 1918 1 64,
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
   opAt 1930 (.Dup dA0),
   opAt 1931 .NOT,
   pushAt 1932 2 1280,
   opAt 1933 .MSTORE]


/-- `blk2919`, first part: `L = d &&& -d` twice on top of `d`, stopping before the `CLZ`. -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1934 (.Dup dA0),
   pushAt 1935 0 0,
   opAt 1936 .SUB,
   opAt 1937 (.Dup dA1),
   opAt 1938 .AND,
   opAt 1939 (.Dup dA0)]


/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1941 (.Dup dA0),
   pushAt 1942 1 1,
   opAt 1943 .ADD,
   pushAt 1944 2 1600,
   opAt 1945 .MSTORE,
   pushAt 1946 1 255,
   opAt 1947 .SUB,
   pushAt 1948 2 1536,
   opAt 1949 .MSTORE,
   opAt 1950 (.Swap ⟨0, by decide⟩),
   opAt 1951 .DIV,
   opAt 1952 (.Dup dA0),
   pushAt 1953 2 1568,
   opAt 1954 .MSTORE,
   opAt 1955 (.Dup dA0),
   opAt 1956 (.Dup dA0),
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
   opAt 1965 (.Dup dA0),
   opAt 1966 (.Dup dA2),
   opAt 1967 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1968 (.Dup dA0),
   pushAt 1969 1 3,
   opAt 1970 .MUL,
   pushAt 1971 1 2,
   opAt 1972 .XOR,
   opAt 1973 (.Dup dA0),
   opAt 1974 (.Dup dA2),
   opAt 1975 .MUL,
   pushAt 1976 1 2,
   opAt 1977 .SUB,
   opAt 1978 .MUL,
   opAt 1979 (.Dup dA0),
   opAt 1980 (.Dup dA2),
   opAt 1981 .MUL,
   pushAt 1982 1 2,
   opAt 1983 .SUB,
   opAt 1984 .MUL,
   opAt 1985 (.Dup dA0),
   opAt 1986 (.Dup dA2),
   opAt 1987 .MUL,
   pushAt 1988 1 2,
   opAt 1989 .SUB,
   opAt 1990 .MUL,
   opAt 1991 (.Dup dA0),
   opAt 1992 (.Dup dA2),
   opAt 1993 .MUL,
   pushAt 1994 1 2,
   opAt 1995 .SUB,
   opAt 1996 .MUL,
   opAt 1997 (.Dup dA0),
   opAt 1998 (.Dup dA2),
   opAt 1999 .MUL,
   pushAt 2000 1 2,
   opAt 2001 .SUB,
   opAt 2002 .MUL,
   opAt 2003 (.Dup dA0),
   opAt 2004 (.Swap sA1),
   opAt 2005 .MUL,
   pushAt 2006 1 2,
   opAt 2007 .SUB,
   opAt 2008 .MUL]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2009 (.Dup ⟨0, by decide⟩),
   opAt 2010 (.Swap ⟨1, by decide⟩),
   opAt 2011 .MUL,
   pushAt 2012 2 1664,
   opAt 2013 .MSTORE,
   opAt 2014 .MUL,
   pushAt 2015 0 0,
   opAt 2016 .SUB,
   pushAt 2017 2 2720,
   opAt 2018 .MSTORE,
   pushAt 2019 4 2310,
   opAt 2020 (.Dup ⟨4, by decide⟩),
   pushAt 2021 1 1,
   opAt 2022 .EQ,
   pushAt 2023 2 2656,
   opAt 2024 .MLOAD,
   opAt 2025 .CALLDATALOAD,
   pushAt 2026 0 0,
   opAt 2027 .BYTE,
   pushAt 2028 1 3,
   opAt 2029 .EQ,
   opAt 2030 .AND,
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
  [opAt 2073 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2074 (.Dup dA15),
   pushAt 2075 2 2112,
   pushAt 2076 2 2080,
   opAt 2077 .MCOPY]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2078 2 2080,
   opAt 2079 .MLOAD,
   opAt 2080 (.Dup dA0),
   opAt 2081 (.Dup dA14),
   opAt 2082 .SHR,
   opAt 2083 (.Swap sA0),
   pushAt 2084 2 1600,
   opAt 2085 .MLOAD,
   opAt 2086 .SHL,
   pushAt 2087 2 2112,
   opAt 2088 .MLOAD,
   opAt 2089 (.Dup dA15),
   opAt 2090 .SHR,
   opAt 2091 .ADD,
   opAt 2092 (.Dup dA13),
   opAt 2093 (.Dup dA0),
   opAt 2094 (.Dup dA13),
   opAt 2095 (.Dup dA4),
   opAt 2096 .MULMOD,
   opAt 2097 (.Dup dA2),
   opAt 2098 .ADDMOD,
   opAt 2099 (.Swap sA0),
   opAt 2100 .SUB,
   opAt 2101 (.Dup dA12),
   opAt 2102 .MUL,
   opAt 2103 (.Dup dA15),
   opAt 2104 (.Dup dA1),
   pushAt 2105 1 128,
   opAt 2106 .SHR,
   opAt 2107 .MUL,
   opAt 2108 (.Dup dA1),
   pushAt 2109 0 0,
   opAt 2110 .MLOAD,
   opAt 2111 .MUL,
   pushAt 2112 2 2112,
   opAt 2113 .MLOAD,
   opAt 2114 .SUB,
   opAt 2115 .LT,
   opAt 2116 (.Swap sA0),
   opAt 2117 .SUB,
   pushAt 2118 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2119 (.Swap sA1),
   opAt 2120 (.Dup dA14),
   opAt 2121 .GT,
   opAt 2122 (.Dup dA2),
   opAt 2123 .ADD,
   opAt 2124 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8250 .JUMPDEST]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8251 (.Dup dA15),
   pushAt 8252 2 2112,
   pushAt 8253 2 2080,
   opAt 8254 .MCOPY]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8255 2 2080,
   opAt 8256 .MLOAD,
   opAt 8257 (.Dup dA0),
   opAt 8258 (.Dup dA14),
   opAt 8259 .SHR,
   opAt 8260 (.Swap sA0),
   pushAt 8261 2 1600,
   opAt 8262 .MLOAD,
   opAt 8263 .SHL,
   pushAt 8264 2 2112,
   opAt 8265 .MLOAD,
   opAt 8266 (.Dup dA15),
   opAt 8267 .SHR,
   opAt 8268 .ADD,
   opAt 8269 (.Dup dA13),
   opAt 8270 (.Dup dA0),
   opAt 8271 (.Dup dA13),
   opAt 8272 (.Dup dA4),
   opAt 8273 .MULMOD,
   opAt 8274 (.Dup dA2),
   opAt 8275 .ADDMOD,
   opAt 8276 (.Swap sA0),
   opAt 8277 .SUB,
   opAt 8278 (.Dup dA12),
   opAt 8279 .MUL,
   opAt 8280 (.Dup dA15),
   opAt 8281 (.Dup dA1),
   pushAt 8282 1 128,
   opAt 8283 .SHR,
   opAt 8284 .MUL,
   opAt 8285 (.Dup dA1),
   pushAt 8286 0 0,
   opAt 8287 .MLOAD,
   opAt 8288 .MUL,
   pushAt 8289 2 2112,
   opAt 8290 .MLOAD,
   opAt 8291 .SUB,
   opAt 8292 .LT,
   opAt 8293 (.Swap sA0),
   opAt 8294 .SUB,
   pushAt 8295 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8296 (.Swap sA1),
   opAt 8297 (.Dup dA14),
   opAt 8298 .GT,
   opAt 8299 (.Dup dA2),
   opAt 8300 .ADD,
   opAt 8301 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/

def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2339 2 2080,
   opAt 2340 .MLOAD,
   opAt 2341 .ADD,
   opAt 2342 .SUB,
   opAt 2343 (.Dup ⟨0, by decide⟩),
   pushAt 2344 2 2080,
   opAt 2345 .MSTORE,
   pushAt 2346 28 3069,
   opAt 2347 .JUMPI]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8404 2 2080,
   opAt 8405 .MLOAD,
   opAt 8406 .ADD,
   opAt 8407 .SUB,
   opAt 8408 (.Dup dA0),
   pushAt 8409 2 2080,
   opAt 8410 .MSTORE,
   pushAt 8411 32 3069,
   opAt 8412 .JUMPI]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2339 2 2080,
   opAt 2340 .MLOAD,
   opAt 2341 .ADD,
   opAt 2342 .SUB,
   opAt 2343 (.Dup ⟨0, by decide⟩),
   pushAt 2344 2 2080,
   opAt 2345 .MSTORE,
   pushAt 2346 28 3069,
   opAt 2347 .JUMPI,
   opAt 2348 .POP,
   pushAt 2349 0 0]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2364 .JUMPDEST,
   opAt 2365 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2366 .JUMPDEST,
   pushAt 2367 0 0,
   pushAt 2368 2 2784,
   opAt 2369 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2370 .JUMPDEST,
   opAt 2371 (.Dup dA0),
   opAt 2372 .MLOAD,
   pushAt 2373 2 2112,
   opAt 2374 (.Dup dA2),
   opAt 2375 .SUB,
   opAt 2376 .MLOAD,
   opAt 2377 (.Dup dA1),
   opAt 2378 .ADD,
   opAt 2379 (.Swap sA0),
   opAt 2380 (.Dup dA1),
   opAt 2381 .LT,
   opAt 2382 (.Swap sA0),
   opAt 2383 (.Dup dA3),
   opAt 2384 .ADD,
   opAt 2385 (.Swap sA2),
   opAt 2386 (.Dup dA3),
   opAt 2387 .LT,
   opAt 2388 .OR,
   opAt 2389 (.Swap sA1),
   opAt 2390 (.Dup dA1),
   opAt 2391 .MSTORE,
   pushAt 2392 1 31,
   opAt 2393 .NOT,
   opAt 2394 .ADD,
   pushAt 2395 2 2111,
   opAt 2396 (.Dup dA1),
   opAt 2397 .GT,
   pushAt 2398 2 3077,
   opAt 2399 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2400 .POP,
   pushAt 2401 2 2080,
   opAt 2402 .MLOAD,
   opAt 2403 (.Dup dA1),
   opAt 2404 .ADD,
   opAt 2405 (.Dup dA0),
   pushAt 2406 2 2080,
   opAt 2407 .MSTORE,
   opAt 2408 .LT,
   opAt 2409 .ISZERO,
   pushAt 2410 2 3071,
   opAt 2411 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2412 2 2080,
   opAt 2413 .MLOAD,
   opAt 2414 (.Dup ⟨0, by decide⟩),
   opAt 2415 .ISZERO,
   pushAt 2416 2 3046,
   opAt 2417 .JUMPI]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2350 .JUMPDEST,
   opAt 2351 .NOT,
   opAt 2352 .ADD,
   opAt 2353 (.Dup ⟨0, by decide⟩),
   opAt 2354 (.Dup ⟨2, by decide⟩),
   opAt 2355 .JUMPI]

def blk3253Last :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2350 .JUMPDEST,
   opAt 2351 .NOT,
   opAt 2352 .ADD,
   opAt 2353 (.Dup ⟨0, by decide⟩),
   opAt 2354 (.Dup ⟨2, by decide⟩),
   opAt 2355 .JUMPI,
   opAt 2356 .JUMPDEST]


/-- The loop exit after the last step: `SHIFT_DONE` is the `JUMPI` fall-through itself (the
exit block sits right behind the bottom test), so the exit path is empty. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- The four-limb private middle block (pc 10941). -/
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8404 2 2080,
   opAt 8405 .MLOAD,
   opAt 8406 .ADD,
   opAt 8407 .SUB,
   opAt 8408 (.Dup dA0),
   pushAt 8409 2 2080,
   opAt 8410 .MSTORE,
   pushAt 8411 32 3069,
   opAt 8412 .JUMPI]

/-- The four-limb private counter (pc 10970; nothing jumps here, so no `JUMPDEST`). -/
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8413 .ADD,
   opAt 8414 (.Dup dA0),
   opAt 8415 (.Dup dA2),
   opAt 8416 .JUMPI]


theorem jumpDest4608 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2357 = true :=
  CycleSubmission.Global.Binding.jumpDest 1868 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 135 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2378 = true :=
  CycleSubmission.Global.Binding.jumpDest 1881 (by rfl)


theorem jumpDestNeg4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true :=
  CycleSubmission.Global.Binding.jumpDest 1813 (by rfl)

theorem jumpDestNegT :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2436 = true :=
  CycleSubmission.Global.Binding.jumpDest 1917 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2660 = true :=
  CycleSubmission.Global.Binding.jumpDest 2073 (by rfl)

/-- The appended four-limb loop head. -/
theorem jumpDestHead4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10692 = true :=
  CycleSubmission.Global.Binding.jumpDest 8250 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3071 = true :=
  CycleSubmission.Global.Binding.jumpDest 2366 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3077 = true :=
  CycleSubmission.Global.Binding.jumpDest 2370 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3069 = true :=
  CycleSubmission.Global.Binding.jumpDest 2364 (by rfl)

theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3046 = true := by
 have h := CycleSubmission.Global.Binding.jumpDest 2350 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
 have hp : CycleSubmission.Artifact.artifact.instructionPC 2350 = 3046 := by
  rw [CycleSubmission.PCCertificate.selectedPC 2350 (by decide)]; decide
 simpa only [hp] using h

theorem jumpDest5366 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3053 = true :=
  CycleSubmission.Global.Binding.jumpDest 2357 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3914 = true :=
  CycleSubmission.Global.Binding.jumpDest 3007 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2298 = true :=
  CycleSubmission.Global.Binding.jumpDest 1822 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2946 + 116·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2057 1 32,
   opAt 2058 .MLOAD,
   pushAt 2059 1 128,
   opAt 2060 .SHR,
   opAt 2061 (.Swap ⟨12, by decide⟩),
   opAt 2062 .POP,
   opAt 2063 (.Dup ⟨15, by decide⟩),
   opAt 2064 .SHR,
   opAt 2065 (.Dup ⟨13, by decide⟩),
   pushAt 2066 2 2008,
   opAt 2067 .MUL,
   pushAt 2068 2 18724,
   opAt 2069 .SUB,
   opAt 2070 (.Swap ⟨0, by decide⟩),
   opAt 2071 (.Dup ⟨1, by decide⟩),
   opAt 2072 .JUMP]

/-- The cleanup tail (pcs 3866-3887): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 3007 .JUMPDEST,
   opAt 3008 .POP,
   opAt 3009 .POP,
   opAt 3010 .POP,
   opAt 3011 .POP,
   opAt 3012 .POP,
   opAt 3013 .POP,
   opAt 3014 .POP,
   opAt 3015 .POP,
   opAt 3016 .POP,
   opAt 3017 .POP,
   opAt 3018 .POP,
   opAt 3019 .POP,
   opAt 3020 .POP,
   opAt 3021 .POP,
   opAt 3022 .POP,
   opAt 3023 .POP,
   pushAt 3024 2 2284,
   opAt 3025 .ADD,
   opAt 3026 .JUMP]

end CycleSubmission.Global.Fast

namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
