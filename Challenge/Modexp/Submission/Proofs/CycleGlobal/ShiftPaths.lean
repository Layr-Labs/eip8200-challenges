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
  [opAt 1856 .JUMPDEST,
   opAt 1857 (.Dup dA0),
   opAt 1858 (.Dup dA3),
   opAt 1859 .XOR,
   pushAt 1860 1 207,
   opAt 1861 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1862 (.Dup dA0),
   pushAt 1863 1 96,
   pushAt 1864 2 2112,
   opAt 1865 .CALLDATACOPY,
   pushAt 1866 2 2378,
   pushAt 1867 2 3484,
   opAt 1868 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1874 (.Dup dA0),
   pushAt 1875 1 128,
   opAt 1876 .EQ,
   pushAt 1877 2 2284,
   opAt 1878 .JUMPI]

/-- Negation cell at pc 2429: `NEG[1504] := 0 - mem[224]`. -/
def negS8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1879 1 224,
   opAt 1880 .MLOAD,
   pushAt 1881 0 0,
   opAt 1882 .SUB,
   pushAt 1883 2 1504,
   opAt 1884 .MSTORE]

/-- Negation cell at pc 2438: `NEG[1472] := NOT mem[192]`. -/
def negN8a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1885 1 192,
   opAt 1886 .MLOAD,
   opAt 1887 .NOT,
   pushAt 1888 2 1472,
   opAt 1889 .MSTORE]

/-- Negation cell at pc 2446: `NEG[1440] := NOT mem[160]`. -/
def negN8b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1890 1 160,
   opAt 1891 .MLOAD,
   opAt 1892 .NOT,
   pushAt 1893 2 1440,
   opAt 1894 .MSTORE]

/-- Negation cell at pc 2454: `NEG[1408] := NOT mem[128]`. -/
def negN8c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1895 1 128,
   opAt 1896 .MLOAD,
   opAt 1897 .NOT,
   pushAt 1898 2 1408,
   opAt 1899 .MSTORE]

/-- Negation cell at pc 2462: `NEG[1376] := NOT mem[96]`. -/
def negN8d :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1900 1 96,
   opAt 1901 .MLOAD,
   opAt 1902 .NOT,
   pushAt 1903 2 1376,
   opAt 1904 .MSTORE]

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
  [opAt 1905 .JUMPDEST]

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
  [opAt 1905 .JUMPDEST,
   pushAt 1906 1 64,
   opAt 1907 .MLOAD,
   opAt 1908 .NOT,
   pushAt 1909 2 1344,
   opAt 1910 .MSTORE,
   pushAt 1911 1 32,
   opAt 1912 .MLOAD,
   opAt 1913 .NOT,
   pushAt 1914 2 1312,
   opAt 1915 .MSTORE,
   pushAt 1916 0 0,
   opAt 1917 .MLOAD,
   opAt 1918 (.Dup dA0),
   opAt 1919 .NOT,
   pushAt 1920 2 1280,
   opAt 1921 .MSTORE]


/-- `blk2919`, first part: `L = d &&& -d` twice on top of `d`, stopping before the `CLZ`. -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1922 (.Dup dA0),
   pushAt 1923 0 0,
   opAt 1924 .SUB,
   opAt 1925 (.Dup dA1),
   opAt 1926 .AND,
   opAt 1927 (.Dup dA0)]


/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1929 (.Dup dA0),
   pushAt 1930 1 1,
   opAt 1931 .ADD,
   pushAt 1932 2 1600,
   opAt 1933 .MSTORE,
   pushAt 1934 1 255,
   opAt 1935 .SUB,
   pushAt 1936 2 1536,
   opAt 1937 .MSTORE,
   opAt 1938 (.Swap ⟨0, by decide⟩),
   opAt 1939 .DIV,
   opAt 1940 (.Dup dA0),
   pushAt 1941 2 1568,
   opAt 1942 .MSTORE,
   opAt 1943 (.Dup dA0),
   opAt 1944 (.Dup dA0),
   pushAt 1945 0 0,
   opAt 1946 .SUB,
   opAt 1947 .MOD,
   pushAt 1948 2 1632,
   opAt 1949 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1950 2 2752,
   opAt 1951 .MLOAD,
   opAt 1952 .MLOAD,
   opAt 1953 (.Dup dA0),
   opAt 1954 (.Dup dA2),
   opAt 1955 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1956 (.Dup dA0),
   pushAt 1957 1 3,
   opAt 1958 .MUL,
   pushAt 1959 1 2,
   opAt 1960 .XOR,
   opAt 1961 (.Dup dA0),
   opAt 1962 (.Dup dA2),
   opAt 1963 .MUL,
   pushAt 1964 1 2,
   opAt 1965 .SUB,
   opAt 1966 .MUL,
   opAt 1967 (.Dup dA0),
   opAt 1968 (.Dup dA2),
   opAt 1969 .MUL,
   pushAt 1970 1 2,
   opAt 1971 .SUB,
   opAt 1972 .MUL,
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
   opAt 1992 (.Swap sA1),
   opAt 1993 .MUL,
   pushAt 1994 1 2,
   opAt 1995 .SUB,
   opAt 1996 .MUL]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1997 (.Dup dA0),
   opAt 1998 (.Swap sA1),
   opAt 1999 .MUL,
   pushAt 2000 2 1664,
   opAt 2001 .MSTORE,
   opAt 2002 .MUL,
   pushAt 2003 0 0,
   opAt 2004 .SUB,
   pushAt 2005 2 2720,
   opAt 2006 .MSTORE,
   pushAt 2007 4 2310,
   opAt 2008 (.Dup dA4),
   pushAt 2009 1 1,
   opAt 2010 .EQ,
   pushAt 2011 2 2656,
   opAt 2012 .MLOAD,
   opAt 2013 .CALLDATALOAD,
   pushAt 2014 0 0,
   opAt 2015 .BYTE,
   pushAt 2016 1 3,
   opAt 2017 .EQ,
   opAt 2018 .AND,
   opAt 2019 (.Dup dA4),
   opAt 2020 (.Dup dA4),
   pushAt 2021 1 32,
   opAt 2022 .MLOAD,
   pushAt 2023 4 128,
   opAt 2024 .SHR,
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
   opAt 2047 (.Dup dA12)]


/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2058 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2059 (.Dup dA15),
   pushAt 2060 2 2112,
   pushAt 2061 2 2080,
   opAt 2062 .MCOPY]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2063 2 2080,
   opAt 2064 .MLOAD,
   opAt 2065 (.Dup dA0),
   opAt 2066 (.Dup dA14),
   opAt 2067 .SHR,
   opAt 2068 (.Swap sA0),
   pushAt 2069 2 1600,
   opAt 2070 .MLOAD,
   opAt 2071 .SHL,
   pushAt 2072 2 2112,
   opAt 2073 .MLOAD,
   opAt 2074 (.Dup dA15),
   opAt 2075 .SHR,
   opAt 2076 .ADD,
   opAt 2077 (.Dup dA13),
   opAt 2078 (.Dup dA0),
   opAt 2079 (.Dup dA13),
   opAt 2080 (.Dup dA4),
   opAt 2081 .MULMOD,
   opAt 2082 (.Dup dA2),
   opAt 2083 .ADDMOD,
   opAt 2084 (.Swap sA0),
   opAt 2085 .SUB,
   opAt 2086 (.Dup dA12),
   opAt 2087 .MUL,
   opAt 2088 (.Dup dA15),
   opAt 2089 (.Dup dA1),
   pushAt 2090 1 128,
   opAt 2091 .SHR,
   opAt 2092 .MUL,
   opAt 2093 (.Dup dA1),
   pushAt 2094 0 0,
   opAt 2095 .MLOAD,
   opAt 2096 .MUL,
   pushAt 2097 2 2112,
   opAt 2098 .MLOAD,
   opAt 2099 .SUB,
   opAt 2100 .LT,
   opAt 2101 (.Swap sA0),
   opAt 2102 .SUB,
   pushAt 2103 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2104 (.Swap sA1),
   opAt 2105 (.Dup dA14),
   opAt 2106 .GT,
   opAt 2107 (.Dup dA2),
   opAt 2108 .ADD,
   opAt 2109 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8213 .JUMPDEST]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8214 (.Dup dA15),
   pushAt 8215 2 2112,
   pushAt 8216 2 2080,
   opAt 8217 .MCOPY]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8218 2 2080,
   opAt 8219 .MLOAD,
   opAt 8220 (.Dup dA0),
   opAt 8221 (.Dup dA14),
   opAt 8222 .SHR,
   opAt 8223 (.Swap sA0),
   pushAt 8224 2 1600,
   opAt 8225 .MLOAD,
   opAt 8226 .SHL,
   pushAt 8227 2 2112,
   opAt 8228 .MLOAD,
   opAt 8229 (.Dup dA15),
   opAt 8230 .SHR,
   opAt 8231 .ADD,
   opAt 8232 (.Dup dA13),
   opAt 8233 (.Dup dA0),
   opAt 8234 (.Dup dA13),
   opAt 8235 (.Dup dA4),
   opAt 8236 .MULMOD,
   opAt 8237 (.Dup dA2),
   opAt 8238 .ADDMOD,
   opAt 8239 (.Swap sA0),
   opAt 8240 .SUB,
   opAt 8241 (.Dup dA12),
   opAt 8242 .MUL,
   opAt 8243 (.Dup dA15),
   opAt 8244 (.Dup dA1),
   pushAt 8245 1 128,
   opAt 8246 .SHR,
   opAt 8247 .MUL,
   opAt 8248 (.Dup dA1),
   pushAt 8249 0 0,
   opAt 8250 .MLOAD,
   opAt 8251 .MUL,
   pushAt 8252 2 2112,
   opAt 8253 .MLOAD,
   opAt 8254 .SUB,
   opAt 8255 .LT,
   opAt 8256 (.Swap sA0),
   opAt 8257 .SUB,
   pushAt 8258 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8259 (.Swap sA1),
   opAt 8260 (.Dup dA14),
   opAt 8261 .GT,
   opAt 8262 (.Dup dA2),
   opAt 8263 .ADD,
   opAt 8264 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/

def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2324 2 2080,
   opAt 2325 .MLOAD,
   opAt 2326 .ADD,
   opAt 2327 .SUB,
   opAt 2328 (.Dup dA0),
   pushAt 2329 2 2080,
   opAt 2330 .MSTORE,
   pushAt 2331 30 3069,
   opAt 2332 .JUMPI]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8367 2 2080,
   opAt 8368 .MLOAD,
   opAt 8369 .ADD,
   opAt 8370 .SUB,
   opAt 8371 (.Dup dA0),
   pushAt 8372 2 2080,
   opAt 8373 .MSTORE,
   pushAt 8374 31 3069,
   opAt 8375 .JUMPI]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2324 2 2080,
   opAt 2325 .MLOAD,
   opAt 2326 .ADD,
   opAt 2327 .SUB,
   opAt 2328 (.Dup dA0),
   pushAt 2329 2 2080,
   opAt 2330 .MSTORE,
   pushAt 2331 30 3069,
   opAt 2332 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2348 .JUMPDEST,
   opAt 2349 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2350 .JUMPDEST,
   pushAt 2351 0 0,
   pushAt 2352 2 2784,
   opAt 2353 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2354 .JUMPDEST,
   opAt 2355 (.Dup dA0),
   opAt 2356 .MLOAD,
   pushAt 2357 2 2112,
   opAt 2358 (.Dup dA2),
   opAt 2359 .SUB,
   opAt 2360 .MLOAD,
   opAt 2361 (.Dup dA1),
   opAt 2362 .ADD,
   opAt 2363 (.Swap sA0),
   opAt 2364 (.Dup dA1),
   opAt 2365 .LT,
   opAt 2366 (.Swap sA0),
   opAt 2367 (.Dup dA3),
   opAt 2368 .ADD,
   opAt 2369 (.Swap sA2),
   opAt 2370 (.Dup dA3),
   opAt 2371 .LT,
   opAt 2372 .OR,
   opAt 2373 (.Swap sA1),
   opAt 2374 (.Dup dA1),
   opAt 2375 .MSTORE,
   pushAt 2376 1 31,
   opAt 2377 .NOT,
   opAt 2378 .ADD,
   pushAt 2379 2 2111,
   opAt 2380 (.Dup dA1),
   opAt 2381 .GT,
   pushAt 2382 2 3077,
   opAt 2383 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2384 .POP,
   pushAt 2385 2 2080,
   opAt 2386 .MLOAD,
   opAt 2387 (.Dup dA1),
   opAt 2388 .ADD,
   opAt 2389 (.Dup dA0),
   pushAt 2390 2 2080,
   opAt 2391 .MSTORE,
   opAt 2392 .LT,
   opAt 2393 .ISZERO,
   pushAt 2394 2 3071,
   opAt 2395 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2396 0 0,
   opAt 2397 .NOT,
   pushAt 2398 6 3046,
   opAt 2399 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2333 .JUMPDEST,
   opAt 2334 .ADD,
   opAt 2335 (.Dup dA0),
   opAt 2336 (.Dup dA2),
   opAt 2337 .JUMPI]

def blk3253Last :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2333 .JUMPDEST,
   opAt 2334 .ADD,
   opAt 2335 (.Dup dA0),
   opAt 2336 (.Dup dA2),
   opAt 2337 .JUMPI]


/-- The loop exit after the last step: `SHIFT_DONE` is the `JUMPI` fall-through itself (the
exit block sits right behind the bottom test), so the exit path is empty. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- The four-limb private middle block (pc 10941). -/
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8367 2 2080,
   opAt 8368 .MLOAD,
   opAt 8369 .ADD,
   opAt 8370 .SUB,
   opAt 8371 (.Dup dA0),
   pushAt 8372 2 2080,
   opAt 8373 .MSTORE,
   pushAt 8374 31 3069,
   opAt 8375 .JUMPI]

/-- The four-limb private counter (pc 10970; nothing jumps here, so no `JUMPDEST`). -/
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8376 .ADD,
   opAt 8377 (.Dup dA0),
   opAt 8378 (.Dup dA2),
   opAt 8379 .JUMPI]


theorem jumpDest4608 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2357 = true :=
  CycleSubmission.Global.Binding.jumpDest 1856 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 135 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2378 = true :=
  CycleSubmission.Global.Binding.jumpDest 1869 (by rfl)


theorem jumpDestNeg4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true :=
  CycleSubmission.Global.Binding.jumpDest 1813 (by rfl)

theorem jumpDestNegT :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2436 = true :=
  CycleSubmission.Global.Binding.jumpDest 1905 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2660 = true :=
  CycleSubmission.Global.Binding.jumpDest 2058 (by rfl)

/-- The appended four-limb loop head. -/
theorem jumpDestHead4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10692 = true :=
  CycleSubmission.Global.Binding.jumpDest 8213 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3071 = true :=
  CycleSubmission.Global.Binding.jumpDest 2350 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3077 = true :=
  CycleSubmission.Global.Binding.jumpDest 2354 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3069 = true :=
  CycleSubmission.Global.Binding.jumpDest 2348 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3046 = true :=
  CycleSubmission.Global.Binding.jumpDest 2333 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3051 = true :=
  CycleSubmission.Global.Binding.jumpDest 2338 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3914 = true :=
  CycleSubmission.Global.Binding.jumpDest 2970 (by rfl)

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
  [opAt 2048 (.Dup dA15),
   opAt 2049 .SHR,
   opAt 2050 (.Dup dA13),
   pushAt 2051 2 2008,
   opAt 2052 .MUL,
   pushAt 2053 2 18724,
   opAt 2054 .SUB,
   opAt 2055 (.Swap sA0),
   opAt 2056 (.Dup dA1),
   opAt 2057 .JUMP]

/-- The cleanup tail (pcs 3866-3887): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2970 .JUMPDEST,
   opAt 2971 .POP,
   opAt 2972 .POP,
   opAt 2973 .POP,
   opAt 2974 .POP,
   opAt 2975 .POP,
   opAt 2976 .POP,
   opAt 2977 .POP,
   opAt 2978 .POP,
   opAt 2979 .POP,
   opAt 2980 .POP,
   opAt 2981 .POP,
   opAt 2982 .POP,
   opAt 2983 .POP,
   opAt 2984 .POP,
   opAt 2985 .POP,
   opAt 2986 .POP,
   pushAt 2987 2 2284,
   opAt 2988 .ADD,
   opAt 2989 .JUMP]

end CycleSubmission.Global.Fast

namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
