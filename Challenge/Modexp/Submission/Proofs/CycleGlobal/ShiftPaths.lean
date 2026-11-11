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
  [opAt 1857 .JUMPDEST,
   opAt 1858 (.Dup dA0),
   opAt 1859 (.Dup dA3),
   opAt 1860 .XOR,
   pushAt 1861 1 207,
   opAt 1862 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1863 (.Dup dA0),
   pushAt 1864 1 96,
   pushAt 1865 2 2112,
   opAt 1866 .CALLDATACOPY,
   pushAt 1867 2 2378,
   pushAt 1868 2 3484,
   opAt 1869 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1875 (.Dup dA0),
   pushAt 1876 1 128,
   opAt 1877 .EQ,
   pushAt 1878 2 2290,
   opAt 1879 .JUMPI]

/-- Negation cell at pc 2429: `NEG[1504] := 0 - mem[224]`. -/
def negS8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1880 1 224,
   opAt 1881 .MLOAD,
   pushAt 1882 0 0,
   opAt 1883 .SUB,
   pushAt 1884 2 1504,
   opAt 1885 .MSTORE]

/-- Negation cell at pc 2438: `NEG[1472] := NOT mem[192]`. -/
def negN8a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1886 1 192,
   opAt 1887 .MLOAD,
   opAt 1888 .NOT,
   pushAt 1889 2 1472,
   opAt 1890 .MSTORE]

/-- Negation cell at pc 2446: `NEG[1440] := NOT mem[160]`. -/
def negN8b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1891 1 160,
   opAt 1892 .MLOAD,
   opAt 1893 .NOT,
   pushAt 1894 2 1440,
   opAt 1895 .MSTORE]

/-- Negation cell at pc 2454: `NEG[1408] := NOT mem[128]`. -/
def negN8c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1896 1 128,
   opAt 1897 .MLOAD,
   opAt 1898 .NOT,
   pushAt 1899 2 1408,
   opAt 1900 .MSTORE]

/-- Negation cell at pc 2462: `NEG[1376] := NOT mem[96]`. -/
def negN8d :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1901 1 96,
   opAt 1902 .MLOAD,
   opAt 1903 .NOT,
   pushAt 1904 2 1376,
   opAt 1905 .MSTORE]

/- Negation cell at pc 2471: `NEG[1344] := NOT mem[64]`. -/


/- Negation cell at pc 2479: `NEG[1312] := NOT mem[32]`. -/


/- Negation cell at pc 2487: `NEG[1280] := NOT mem[0]`. -/


/-- Negation cell at pc 2337: `NEG[1376] := 0 - mem[96]`. -/
def negS4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1818 1 96,
   opAt 1819 .MLOAD,
   pushAt 1820 0 0,
   opAt 1821 .SUB,
   pushAt 1822 2 1376,
   opAt 1823 .MSTORE]

/-- The four-limb stub's `JUMPDEST` (pc 2336). -/
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1817 .JUMPDEST]

/-- The four-limb stub joins `NEG_TAIL` (pc 2470). -/
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1824 2 2436,
   opAt 1825 .JUMP]

/-- `NEG_TAIL`'s `JUMPDEST` (pc 2470). -/
def negJT :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1906 .JUMPDEST]

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
  [opAt 1906 .JUMPDEST,
   pushAt 1907 1 64,
   opAt 1908 .MLOAD,
   opAt 1909 .NOT,
   pushAt 1910 2 1344,
   opAt 1911 .MSTORE,
   pushAt 1912 1 32,
   opAt 1913 .MLOAD,
   opAt 1914 .NOT,
   pushAt 1915 2 1312,
   opAt 1916 .MSTORE,
   pushAt 1917 0 0,
   opAt 1918 .MLOAD,
   opAt 1919 (.Dup dA0),
   opAt 1920 .NOT,
   pushAt 1921 2 1280,
   opAt 1922 .MSTORE]


/-- `blk2919`, first part: `L = d &&& -d` twice on top of `d`, stopping before the `CLZ`. -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1923 (.Dup dA0),
   pushAt 1924 0 0,
   opAt 1925 .SUB,
   opAt 1926 (.Dup dA1),
   opAt 1927 .AND,
   opAt 1928 (.Dup dA0)]


/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1930 (.Dup dA0),
   pushAt 1931 1 1,
   opAt 1932 .ADD,
   pushAt 1933 2 1600,
   opAt 1934 .MSTORE,
   pushAt 1935 1 255,
   opAt 1936 .SUB,
   pushAt 1937 2 1536,
   opAt 1938 .MSTORE,
   opAt 1939 (.Swap ⟨0, by decide⟩),
   opAt 1940 .DIV,
   opAt 1941 (.Dup dA0),
   pushAt 1942 2 1568,
   opAt 1943 .MSTORE,
   opAt 1944 (.Dup dA0),
   opAt 1945 (.Dup dA0),
   pushAt 1946 0 0,
   opAt 1947 .SUB,
   opAt 1948 .MOD,
   pushAt 1949 2 1632,
   opAt 1950 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1951 2 2752,
   opAt 1952 .MLOAD,
   opAt 1953 .MLOAD,
   opAt 1954 (.Dup dA0),
   opAt 1955 (.Dup dA2),
   opAt 1956 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1957 (.Dup dA0),
   pushAt 1958 1 3,
   opAt 1959 .MUL,
   pushAt 1960 1 2,
   opAt 1961 .XOR,
   opAt 1962 (.Dup dA0),
   opAt 1963 (.Dup dA2),
   opAt 1964 .MUL,
   pushAt 1965 1 2,
   opAt 1966 .SUB,
   opAt 1967 .MUL,
   opAt 1968 (.Dup dA0),
   opAt 1969 (.Dup dA2),
   opAt 1970 .MUL,
   pushAt 1971 1 2,
   opAt 1972 .SUB,
   opAt 1973 .MUL,
   opAt 1974 (.Dup dA0),
   opAt 1975 (.Dup dA2),
   opAt 1976 .MUL,
   pushAt 1977 1 2,
   opAt 1978 .SUB,
   opAt 1979 .MUL,
   opAt 1980 (.Dup dA0),
   opAt 1981 (.Dup dA2),
   opAt 1982 .MUL,
   pushAt 1983 1 2,
   opAt 1984 .SUB,
   opAt 1985 .MUL,
   opAt 1986 (.Dup dA0),
   opAt 1987 (.Dup dA2),
   opAt 1988 .MUL,
   pushAt 1989 1 2,
   opAt 1990 .SUB,
   opAt 1991 .MUL,
   opAt 1992 (.Dup dA0),
   opAt 1993 (.Swap sA1),
   opAt 1994 .MUL,
   pushAt 1995 1 2,
   opAt 1996 .SUB,
   opAt 1997 .MUL]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1998 (.Dup dA0),
   opAt 1999 (.Swap sA1),
   opAt 2000 .MUL,
   pushAt 2001 2 1664,
   opAt 2002 .MSTORE,
   opAt 2003 .MUL,
   pushAt 2004 0 0,
   opAt 2005 .SUB,
   pushAt 2006 2 2720,
   opAt 2007 .MSTORE,
   pushAt 2008 4 2312,
   opAt 2009 (.Dup dA4),
   pushAt 2010 1 1,
   opAt 2011 .EQ,
   pushAt 2012 2 2656,
   opAt 2013 .MLOAD,
   opAt 2014 .CALLDATALOAD,
   pushAt 2015 0 0,
   opAt 2016 .BYTE,
   pushAt 2017 1 3,
   opAt 2018 .EQ,
   opAt 2019 .AND,
   opAt 2020 (.Dup dA4),
   opAt 2021 (.Dup dA4),
   pushAt 2022 1 32,
   opAt 2023 .MLOAD,
   pushAt 2024 4 128,
   opAt 2025 .SHR,
   pushAt 2026 2 1536,
   opAt 2027 .MLOAD,
   pushAt 2028 2 1568,
   opAt 2029 .MLOAD,
   pushAt 2030 2 1664,
   opAt 2031 .MLOAD,
   pushAt 2032 2 1632,
   opAt 2033 .MLOAD,
   pushAt 2034 2 1504,
   opAt 2035 .MLOAD,
   pushAt 2036 2 1472,
   opAt 2037 .MLOAD,
   pushAt 2038 2 1440,
   opAt 2039 .MLOAD,
   pushAt 2040 2 1408,
   opAt 2041 .MLOAD,
   pushAt 2042 2 1376,
   opAt 2043 .MLOAD,
   pushAt 2044 2 1344,
   opAt 2045 .MLOAD,
   pushAt 2046 2 1312,
   opAt 2047 .MLOAD,
   opAt 2048 (.Dup dA12)]


/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2059 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2060 (.Dup dA15),
   pushAt 2061 2 2112,
   pushAt 2062 2 2080,
   opAt 2063 .MCOPY]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2064 2 2080,
   opAt 2065 .MLOAD,
   opAt 2066 (.Dup dA0),
   opAt 2067 (.Dup dA14),
   opAt 2068 .SHR,
   opAt 2069 (.Swap sA0),
   pushAt 2070 2 1600,
   opAt 2071 .MLOAD,
   opAt 2072 .SHL,
   pushAt 2073 2 2112,
   opAt 2074 .MLOAD,
   opAt 2075 (.Dup dA15),
   opAt 2076 .SHR,
   opAt 2077 .ADD,
   opAt 2078 (.Dup dA13),
   opAt 2079 (.Dup dA0),
   opAt 2080 (.Dup dA13),
   opAt 2081 (.Dup dA4),
   opAt 2082 .MULMOD,
   opAt 2083 (.Dup dA2),
   opAt 2084 .ADDMOD,
   opAt 2085 (.Swap sA0),
   opAt 2086 .SUB,
   opAt 2087 (.Dup dA12),
   opAt 2088 .MUL,
   opAt 2089 (.Dup dA15),
   opAt 2090 (.Dup dA1),
   pushAt 2091 1 128,
   opAt 2092 .SHR,
   opAt 2093 .MUL,
   opAt 2094 (.Dup dA1),
   pushAt 2095 0 0,
   opAt 2096 .MLOAD,
   opAt 2097 .MUL,
   pushAt 2098 2 2112,
   opAt 2099 .MLOAD,
   opAt 2100 .SUB,
   opAt 2101 .LT,
   opAt 2102 (.Swap sA0),
   opAt 2103 .SUB,
   pushAt 2104 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2105 (.Swap sA1),
   opAt 2106 (.Dup dA14),
   opAt 2107 .GT,
   opAt 2108 (.Dup dA2),
   opAt 2109 .ADD,
   opAt 2110 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8218 .JUMPDEST]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8219 (.Dup dA15),
   pushAt 8220 2 2112,
   pushAt 8221 2 2080,
   opAt 8222 .MCOPY]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8223 2 2080,
   opAt 8224 .MLOAD,
   opAt 8225 (.Dup dA0),
   opAt 8226 (.Dup dA14),
   opAt 8227 .SHR,
   opAt 8228 (.Swap sA0),
   pushAt 8229 2 1600,
   opAt 8230 .MLOAD,
   opAt 8231 .SHL,
   pushAt 8232 2 2112,
   opAt 8233 .MLOAD,
   opAt 8234 (.Dup dA15),
   opAt 8235 .SHR,
   opAt 8236 .ADD,
   opAt 8237 (.Dup dA13),
   opAt 8238 (.Dup dA0),
   opAt 8239 (.Dup dA13),
   opAt 8240 (.Dup dA4),
   opAt 8241 .MULMOD,
   opAt 8242 (.Dup dA2),
   opAt 8243 .ADDMOD,
   opAt 8244 (.Swap sA0),
   opAt 8245 .SUB,
   opAt 8246 (.Dup dA12),
   opAt 8247 .MUL,
   opAt 8248 (.Dup dA15),
   opAt 8249 (.Dup dA1),
   pushAt 8250 1 128,
   opAt 8251 .SHR,
   opAt 8252 .MUL,
   opAt 8253 (.Dup dA1),
   pushAt 8254 0 0,
   opAt 8255 .MLOAD,
   opAt 8256 .MUL,
   pushAt 8257 2 2112,
   opAt 8258 .MLOAD,
   opAt 8259 .SUB,
   opAt 8260 .LT,
   opAt 8261 (.Swap sA0),
   opAt 8262 .SUB,
   pushAt 8263 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8264 (.Swap sA1),
   opAt 8265 (.Dup dA14),
   opAt 8266 .GT,
   opAt 8267 (.Dup dA2),
   opAt 8268 .ADD,
   opAt 8269 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/

def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2325 2 2080,
   opAt 2326 .MLOAD,
   opAt 2327 .ADD,
   opAt 2328 .SUB,
   opAt 2329 (.Dup dA0),
   pushAt 2330 2 2080,
   opAt 2331 .MSTORE,
   pushAt 2332 14 3069,
   opAt 2333 .JUMPI]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8372 2 2080,
   opAt 8373 .MLOAD,
   opAt 8374 .ADD,
   opAt 8375 .SUB,
   opAt 8376 (.Dup dA0),
   pushAt 8377 2 2080,
   opAt 8378 .MSTORE,
   pushAt 8379 15 3069,
   opAt 8380 .JUMPI]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2325 2 2080,
   opAt 2326 .MLOAD,
   opAt 2327 .ADD,
   opAt 2328 .SUB,
   opAt 2329 (.Dup dA0),
   pushAt 2330 2 2080,
   opAt 2331 .MSTORE,
   pushAt 2332 14 3069,
   opAt 2333 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2353 .JUMPDEST,
   opAt 2354 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2355 .JUMPDEST,
   pushAt 2356 0 0,
   pushAt 2357 2 2784,
   opAt 2358 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2359 .JUMPDEST,
   opAt 2360 (.Dup dA0),
   opAt 2361 .MLOAD,
   pushAt 2362 2 2112,
   opAt 2363 (.Dup dA2),
   opAt 2364 .SUB,
   opAt 2365 .MLOAD,
   opAt 2366 (.Dup dA1),
   opAt 2367 .ADD,
   opAt 2368 (.Swap sA0),
   opAt 2369 (.Dup dA1),
   opAt 2370 .LT,
   opAt 2371 (.Swap sA0),
   opAt 2372 (.Dup dA3),
   opAt 2373 .ADD,
   opAt 2374 (.Swap sA2),
   opAt 2375 (.Dup dA3),
   opAt 2376 .LT,
   opAt 2377 .OR,
   opAt 2378 (.Swap sA1),
   opAt 2379 (.Dup dA1),
   opAt 2380 .MSTORE,
   pushAt 2381 1 31,
   opAt 2382 .NOT,
   opAt 2383 .ADD,
   pushAt 2384 2 2111,
   opAt 2385 (.Dup dA1),
   opAt 2386 .GT,
   pushAt 2387 2 3077,
   opAt 2388 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2389 .POP,
   pushAt 2390 2 2080,
   opAt 2391 .MLOAD,
   opAt 2392 (.Dup dA1),
   opAt 2393 .ADD,
   opAt 2394 (.Dup dA0),
   pushAt 2395 2 2080,
   opAt 2396 .MSTORE,
   opAt 2397 .LT,
   opAt 2398 .ISZERO,
   pushAt 2399 2 3071,
   opAt 2400 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2401 0 0,
   opAt 2402 .NOT,
   pushAt 2403 6 3030,
   opAt 2404 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2334 .JUMPDEST,
   opAt 2335 .ADD,
   opAt 2336 (.Dup dA0),
   opAt 2337 (.Dup dA2),
   opAt 2338 .JUMPI]

def blk3253Last :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2334 .JUMPDEST,
   opAt 2335 .ADD,
   opAt 2336 (.Dup dA0),
   opAt 2337 (.Dup dA2),
   opAt 2338 .JUMPI]


/-- The loop exit after the last step: `SHIFT_DONE` is the `JUMPI` fall-through itself (the
exit block sits right behind the bottom test), so the exit path is empty. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- The four-limb private middle block (pc 10941). -/
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8372 2 2080,
   opAt 8373 .MLOAD,
   opAt 8374 .ADD,
   opAt 8375 .SUB,
   opAt 8376 (.Dup dA0),
   pushAt 8377 2 2080,
   opAt 8378 .MSTORE,
   pushAt 8379 15 3069,
   opAt 8380 .JUMPI]

/-- The four-limb private counter (pc 10970; nothing jumps here, so no `JUMPDEST`). -/
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8381 .ADD,
   opAt 8382 (.Dup dA0),
   opAt 8383 (.Dup dA2),
   opAt 8384 .JUMPI]


theorem jumpDest4608 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2357 = true :=
  CycleSubmission.Global.Binding.jumpDest 1857 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 135 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2378 = true :=
  CycleSubmission.Global.Binding.jumpDest 1870 (by rfl)


theorem jumpDestNeg4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2290 = true :=
  CycleSubmission.Global.Binding.jumpDest 1817 (by rfl)

theorem jumpDestNegT :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2436 = true :=
  CycleSubmission.Global.Binding.jumpDest 1906 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2660 = true :=
  CycleSubmission.Global.Binding.jumpDest 2059 (by rfl)

/-- The appended four-limb loop head. -/
theorem jumpDestHead4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10692 = true :=
  CycleSubmission.Global.Binding.jumpDest 8218 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3071 = true :=
  CycleSubmission.Global.Binding.jumpDest 2355 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3077 = true :=
  CycleSubmission.Global.Binding.jumpDest 2359 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3069 = true :=
  CycleSubmission.Global.Binding.jumpDest 2353 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3030 = true :=
  CycleSubmission.Global.Binding.jumpDest 2334 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3035 = true :=
  CycleSubmission.Global.Binding.jumpDest 2339 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3914 = true :=
  CycleSubmission.Global.Binding.jumpDest 2975 (by rfl)

/-- `e3go` (pc 2471): the dispatcher's E3 hit block, where the cleanup tail lands after the
E3 phase switch has set the last riding slot to `30`. -/
theorem jumpDest2471 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2304 = true :=
  CycleSubmission.Global.Binding.jumpDest 1826 (by rfl)

/-- The cache-setup block (`E5`, pcs 2764-2810): computes the unrolled-conversion
entry `2946 + 116·[n = 4]`, stores it at `0x6a2` (1698) and the squaring flag at
`0x6e0` (1760), and leaves the loop counter `n ≫ flag` on top of the riding slots
with the entry parked in the scratch slot. -/
def blk2764 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2049 (.Dup dA15),
   opAt 2050 .SHR,
   opAt 2051 (.Dup dA13),
   pushAt 2052 2 2008,
   opAt 2053 .MUL,
   pushAt 2054 2 18724,
   opAt 2055 .SUB,
   opAt 2056 (.Swap sA0),
   opAt 2057 (.Dup dA1),
   opAt 2058 .JUMP]

/-- The cleanup tail (pcs 3866-3887): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2975 .JUMPDEST,
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
   opAt 2987 .POP,
   opAt 2988 .POP,
   opAt 2989 .POP,
   opAt 2990 .POP,
   opAt 2991 .POP,
   pushAt 2992 2 2284,
   opAt 2993 .ADD,
   opAt 2994 .JUMP]

end CycleSubmission.Global.Fast

namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
