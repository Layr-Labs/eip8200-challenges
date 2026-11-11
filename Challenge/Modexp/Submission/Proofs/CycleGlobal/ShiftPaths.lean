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
  [opAt 1854 .JUMPDEST,
   opAt 1855 (.Dup dA0),
   opAt 1856 (.Dup dA3),
   opAt 1857 .XOR,
   pushAt 1858 1 207,
   opAt 1859 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1860 (.Dup dA0),
   pushAt 1861 1 96,
   pushAt 1862 2 2112,
   opAt 1863 .CALLDATACOPY,
   pushAt 1864 2 2378,
   pushAt 1865 2 3484,
   opAt 1866 .JUMP]


/-- The negation width test (negun): `32 n = 128` jumps to the four-limb stub at pc 2336. -/
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1872 (.Dup dA0),
   pushAt 1873 1 128,
   opAt 1874 .EQ,
   pushAt 1875 2 2284,
   opAt 1876 .JUMPI]

/-- Negation cell at pc 2429: `NEG[1504] := 0 - mem[224]`. -/
def negS8 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1877 1 224,
   opAt 1878 .MLOAD,
   pushAt 1879 0 0,
   opAt 1880 .SUB,
   pushAt 1881 2 1504,
   opAt 1882 .MSTORE]

/-- Negation cell at pc 2438: `NEG[1472] := NOT mem[192]`. -/
def negN8a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1883 1 192,
   opAt 1884 .MLOAD,
   opAt 1885 .NOT,
   pushAt 1886 2 1472,
   opAt 1887 .MSTORE]

/-- Negation cell at pc 2446: `NEG[1440] := NOT mem[160]`. -/
def negN8b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1888 1 160,
   opAt 1889 .MLOAD,
   opAt 1890 .NOT,
   pushAt 1891 2 1440,
   opAt 1892 .MSTORE]

/-- Negation cell at pc 2454: `NEG[1408] := NOT mem[128]`. -/
def negN8c :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1893 1 128,
   opAt 1894 .MLOAD,
   opAt 1895 .NOT,
   pushAt 1896 2 1408,
   opAt 1897 .MSTORE]

/-- Negation cell at pc 2462: `NEG[1376] := NOT mem[96]`. -/
def negN8d :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1898 1 96,
   opAt 1899 .MLOAD,
   opAt 1900 .NOT,
   pushAt 1901 2 1376,
   opAt 1902 .MSTORE]

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
  [opAt 1903 .JUMPDEST]

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
  [opAt 1903 .JUMPDEST,
   pushAt 1904 1 64,
   opAt 1905 .MLOAD,
   opAt 1906 .NOT,
   pushAt 1907 2 1344,
   opAt 1908 .MSTORE,
   pushAt 1909 1 32,
   opAt 1910 .MLOAD,
   opAt 1911 .NOT,
   pushAt 1912 2 1312,
   opAt 1913 .MSTORE,
   pushAt 1914 0 0,
   opAt 1915 .MLOAD,
   opAt 1916 (.Dup dA0),
   opAt 1917 .NOT,
   pushAt 1918 2 1280,
   opAt 1919 .MSTORE]


/-- `blk2919`, first part: `L = d &&& -d` twice on top of `d`, stopping before the `CLZ`. -/
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1920 (.Dup dA0),
   pushAt 1921 0 0,
   opAt 1922 .SUB,
   opAt 1923 (.Dup dA1),
   opAt 1924 .AND,
   opAt 1925 (.Dup dA0)]


/-- `blk2919`, second part (pc 2673..2704), after the `CLZ`: `PRE_X := 0 - ~clz L`,
`PRE_L := 255 - clz L`, `PRE_DODD := d / L`, `PRE_BMOD := -dodd mod dodd`. -/
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1927 (.Dup dA0),
   pushAt 1928 1 1,
   opAt 1929 .ADD,
   pushAt 1930 2 1600,
   opAt 1931 .MSTORE,
   pushAt 1932 1 255,
   opAt 1933 .SUB,
   pushAt 1934 2 1536,
   opAt 1935 .MSTORE,
   opAt 1936 (.Swap ⟨0, by decide⟩),
   opAt 1937 .DIV,
   opAt 1938 (.Dup dA0),
   pushAt 1939 2 1568,
   opAt 1940 .MSTORE,
   opAt 1941 (.Dup dA0),
   opAt 1942 (.Dup dA0),
   pushAt 1943 0 0,
   opAt 1944 .SUB,
   opAt 1945 .MOD,
   pushAt 1946 2 1632,
   opAt 1947 .MSTORE]

/-- newton-batch head (pc 2535): load `n0 = mem[mem[0xac0]]` and form `dodd * n0` (inl693: the chain is inline). -/
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 1948 2 2752,
   opAt 1949 .MLOAD,
   opAt 1950 .MLOAD,
   opAt 1951 (.Dup dA0),
   opAt 1952 (.Dup dA2),
   opAt 1953 .MUL]

/-- The inlined Newton chain (pc 2543): `[p] ++ rest` becomes `[newton8W p] ++ rest`. -/
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1954 (.Dup dA0),
   pushAt 1955 1 3,
   opAt 1956 .MUL,
   pushAt 1957 1 2,
   opAt 1958 .XOR,
   opAt 1959 (.Dup dA0),
   opAt 1960 (.Dup dA2),
   opAt 1961 .MUL,
   pushAt 1962 1 2,
   opAt 1963 .SUB,
   opAt 1964 .MUL,
   opAt 1965 (.Dup dA0),
   opAt 1966 (.Dup dA2),
   opAt 1967 .MUL,
   pushAt 1968 1 2,
   opAt 1969 .SUB,
   opAt 1970 .MUL,
   opAt 1971 (.Dup dA0),
   opAt 1972 (.Dup dA2),
   opAt 1973 .MUL,
   pushAt 1974 1 2,
   opAt 1975 .SUB,
   opAt 1976 .MUL,
   opAt 1977 (.Dup dA0),
   opAt 1978 (.Dup dA2),
   opAt 1979 .MUL,
   pushAt 1980 1 2,
   opAt 1981 .SUB,
   opAt 1982 .MUL,
   opAt 1983 (.Dup dA0),
   opAt 1984 (.Dup dA2),
   opAt 1985 .MUL,
   pushAt 1986 1 2,
   opAt 1987 .SUB,
   opAt 1988 .MUL,
   opAt 1989 (.Dup dA0),
   opAt 1990 (.Swap sA1),
   opAt 1991 .MUL,
   pushAt 1992 1 2,
   opAt 1993 .SUB,
   opAt 1994 .MUL]

/-- newton-batch tail (pc 2741): `dinv := x * n0`, `V_MINV := -(dodd * x)`, drop the four
words, then the old `k := n` prologue. -/
def blkNbTail :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 1995 (.Dup dA0),
   opAt 1996 (.Swap sA1),
   opAt 1997 .MUL,
   pushAt 1998 2 1664,
   opAt 1999 .MSTORE,
   opAt 2000 .MUL,
   pushAt 2001 0 0,
   opAt 2002 .SUB,
   pushAt 2003 2 2720,
   opAt 2004 .MSTORE,
   pushAt 2005 4 2310,
   opAt 2006 (.Dup dA4),
   pushAt 2007 1 1,
   opAt 2008 .EQ,
   pushAt 2009 2 2656,
   opAt 2010 .MLOAD,
   opAt 2011 .CALLDATALOAD,
   pushAt 2012 0 0,
   opAt 2013 .BYTE,
   pushAt 2014 1 3,
   opAt 2015 .EQ,
   opAt 2016 .AND,
   opAt 2017 (.Dup dA4),
   opAt 2018 (.Dup dA4),
   pushAt 2019 1 32,
   opAt 2020 .MLOAD,
   pushAt 2021 4 128,
   opAt 2022 .SHR,
   pushAt 2023 2 1536,
   opAt 2024 .MLOAD,
   pushAt 2025 2 1568,
   opAt 2026 .MLOAD,
   pushAt 2027 2 1664,
   opAt 2028 .MLOAD,
   pushAt 2029 2 1632,
   opAt 2030 .MLOAD,
   pushAt 2031 2 1504,
   opAt 2032 .MLOAD,
   pushAt 2033 2 1472,
   opAt 2034 .MLOAD,
   pushAt 2035 2 1440,
   opAt 2036 .MLOAD,
   pushAt 2037 2 1408,
   opAt 2038 .MLOAD,
   pushAt 2039 2 1376,
   opAt 2040 .MLOAD,
   pushAt 2041 2 1344,
   opAt 2042 .MLOAD,
   pushAt 2043 2 1312,
   opAt 2044 .MLOAD,
   opAt 2045 (.Dup dA12)]


/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2056 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2057 (.Dup dA15),
   pushAt 2058 2 2112,
   pushAt 2059 2 2080,
   opAt 2060 .MCOPY]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2061 2 2080,
   opAt 2062 .MLOAD,
   opAt 2063 (.Dup dA0),
   opAt 2064 (.Dup dA14),
   opAt 2065 .SHR,
   opAt 2066 (.Swap sA0),
   pushAt 2067 2 1600,
   opAt 2068 .MLOAD,
   opAt 2069 .SHL,
   pushAt 2070 2 2112,
   opAt 2071 .MLOAD,
   opAt 2072 (.Dup dA15),
   opAt 2073 .SHR,
   opAt 2074 .ADD,
   opAt 2075 (.Dup dA13),
   opAt 2076 (.Dup dA0),
   opAt 2077 (.Dup dA13),
   opAt 2078 (.Dup dA4),
   opAt 2079 .MULMOD,
   opAt 2080 (.Dup dA2),
   opAt 2081 .ADDMOD,
   opAt 2082 (.Swap sA0),
   opAt 2083 .SUB,
   opAt 2084 (.Dup dA12),
   opAt 2085 .MUL,
   opAt 2086 (.Dup dA15),
   opAt 2087 (.Dup dA1),
   pushAt 2088 1 128,
   opAt 2089 .SHR,
   opAt 2090 .MUL,
   opAt 2091 (.Dup dA1),
   pushAt 2092 0 0,
   opAt 2093 .MLOAD,
   opAt 2094 .MUL,
   pushAt 2095 2 2112,
   opAt 2096 .MLOAD,
   opAt 2097 .SUB,
   opAt 2098 .LT,
   opAt 2099 (.Swap sA0),
   opAt 2100 .SUB,
   pushAt 2101 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2102 (.Swap sA1),
   opAt 2103 (.Dup dA14),
   opAt 2104 .GT,
   opAt 2105 (.Dup dA2),
   opAt 2106 .ADD,
   opAt 2107 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8211 .JUMPDEST]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8212 (.Dup dA15),
   pushAt 8213 2 2112,
   pushAt 8214 2 2080,
   opAt 8215 .MCOPY]

/-- The appended four-limb loop head (pc 10726): a byte copy of the eight-limb head. -/
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8216 2 2080,
   opAt 8217 .MLOAD,
   opAt 8218 (.Dup dA0),
   opAt 8219 (.Dup dA14),
   opAt 8220 .SHR,
   opAt 8221 (.Swap sA0),
   pushAt 8222 2 1600,
   opAt 8223 .MLOAD,
   opAt 8224 .SHL,
   pushAt 8225 2 2112,
   opAt 8226 .MLOAD,
   opAt 8227 (.Dup dA15),
   opAt 8228 .SHR,
   opAt 8229 .ADD,
   opAt 8230 (.Dup dA13),
   opAt 8231 (.Dup dA0),
   opAt 8232 (.Dup dA13),
   opAt 8233 (.Dup dA4),
   opAt 8234 .MULMOD,
   opAt 8235 (.Dup dA2),
   opAt 8236 .ADDMOD,
   opAt 8237 (.Swap sA0),
   opAt 8238 .SUB,
   opAt 8239 (.Dup dA12),
   opAt 8240 .MUL,
   opAt 8241 (.Dup dA15),
   opAt 8242 (.Dup dA1),
   pushAt 8243 1 128,
   opAt 8244 .SHR,
   opAt 8245 .MUL,
   opAt 8246 (.Dup dA1),
   pushAt 8247 0 0,
   opAt 8248 .MLOAD,
   opAt 8249 .MUL,
   pushAt 8250 2 2112,
   opAt 8251 .MLOAD,
   opAt 8252 .SUB,
   opAt 8253 .LT,
   opAt 8254 (.Swap sA0),
   opAt 8255 .SUB,
   pushAt 8256 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 8257 (.Swap sA1),
   opAt 8258 (.Dup dA14),
   opAt 8259 .GT,
   opAt 8260 (.Dup dA2),
   opAt 8261 .ADD,
   opAt 8262 .OR]



/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`.
Instructions 2578..2579 are `SWAP3 POP` (pc 3184..3185): they lift the `2^256-1` mask that the
three `JUMPDEST`s at pc 3168..3170 left in place and drop it, restoring the `[carry, q]` shape
before `SUB`. -/

def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2322 2 2080,
   opAt 2323 .MLOAD,
   opAt 2324 .ADD,
   opAt 2325 .SUB,
   opAt 2326 (.Dup dA0),
   pushAt 2327 2 2080,
   opAt 2328 .MSTORE,
   pushAt 2329 31 3069,
   opAt 2330 .JUMPI]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8365 2 2080,
   opAt 8366 .MLOAD,
   opAt 8367 .ADD,
   opAt 8368 .SUB,
   opAt 8369 (.Dup dA0),
   pushAt 8370 2 2080,
   opAt 8371 .MSTORE,
   pushAt 8372 32 3069,
   opAt 8373 .JUMPI]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2322 2 2080,
   opAt 2323 .MLOAD,
   opAt 2324 .ADD,
   opAt 2325 .SUB,
   opAt 2326 (.Dup dA0),
   pushAt 2327 2 2080,
   opAt 2328 .MSTORE,
   pushAt 2329 31 3069,
   opAt 2330 .JUMPI]

/-- `UNC`: entered only with `neg ≠ 0`; drops it and falls into `ADD_LOOP`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2344 .JUMPDEST,
   opAt 2345 .POP]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2346 .JUMPDEST,
   pushAt 2347 0 0,
   pushAt 2348 2 2784,
   opAt 2349 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2350 .JUMPDEST,
   opAt 2351 (.Dup dA0),
   opAt 2352 .MLOAD,
   pushAt 2353 2 2112,
   opAt 2354 (.Dup dA2),
   opAt 2355 .SUB,
   opAt 2356 .MLOAD,
   opAt 2357 (.Dup dA1),
   opAt 2358 .ADD,
   opAt 2359 (.Swap sA0),
   opAt 2360 (.Dup dA1),
   opAt 2361 .LT,
   opAt 2362 (.Swap sA0),
   opAt 2363 (.Dup dA3),
   opAt 2364 .ADD,
   opAt 2365 (.Swap sA2),
   opAt 2366 (.Dup dA3),
   opAt 2367 .LT,
   opAt 2368 .OR,
   opAt 2369 (.Swap sA1),
   opAt 2370 (.Dup dA1),
   opAt 2371 .MSTORE,
   pushAt 2372 1 31,
   opAt 2373 .NOT,
   opAt 2374 .ADD,
   pushAt 2375 2 2111,
   opAt 2376 (.Dup dA1),
   opAt 2377 .GT,
   pushAt 2378 2 3077,
   opAt 2379 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2380 .POP,
   pushAt 2381 2 2080,
   opAt 2382 .MLOAD,
   opAt 2383 (.Dup dA1),
   opAt 2384 .ADD,
   opAt 2385 (.Dup dA0),
   pushAt 2386 2 2080,
   opAt 2387 .MSTORE,
   opAt 2388 .LT,
   opAt 2389 .ISZERO,
   pushAt 2390 2 3071,
   opAt 2391 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 2392 0 0,
   opAt 2393 .NOT,
   pushAt 2394 6 3047,
   opAt 2395 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), back to the loop head while `k ≠ 0` (the `CSUB` call is the identity on every reachable state). -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2331 .JUMPDEST,
   opAt 2332 .ADD,
   opAt 2333 (.Dup dA0),
   opAt 2334 (.Dup dA2),
   opAt 2335 .JUMPI]

def blk3253Last :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2331 .JUMPDEST,
   opAt 2332 .ADD,
   opAt 2333 (.Dup dA0),
   opAt 2334 (.Dup dA2),
   opAt 2335 .JUMPI,
   opAt 2336 .JUMPDEST]


/-- The loop exit after the last step: `SHIFT_DONE` is the `JUMPI` fall-through itself (the
exit block sits right behind the bottom test), so the exit path is empty. -/
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  []

/-- The four-limb private middle block (pc 10941). -/
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 8365 2 2080,
   opAt 8366 .MLOAD,
   opAt 8367 .ADD,
   opAt 8368 .SUB,
   opAt 8369 (.Dup dA0),
   pushAt 8370 2 2080,
   opAt 8371 .MSTORE,
   pushAt 8372 32 3069,
   opAt 8373 .JUMPI]

/-- The four-limb private counter (pc 10970; nothing jumps here, so no `JUMPDEST`). -/
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 8374 .ADD,
   opAt 8375 (.Dup dA0),
   opAt 8376 (.Dup dA2),
   opAt 8377 .JUMPI]


theorem jumpDest4608 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2357 = true :=
  CycleSubmission.Global.Binding.jumpDest 1854 (by rfl)

/-- `modexpBig`, where the trampoline lands. -/
theorem jumpDestBigC :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true :=
  CycleSubmission.Global.Binding.jumpDest 135 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2378 = true :=
  CycleSubmission.Global.Binding.jumpDest 1867 (by rfl)


theorem jumpDestNeg4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2284 = true :=
  CycleSubmission.Global.Binding.jumpDest 1813 (by rfl)

theorem jumpDestNegT :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2436 = true :=
  CycleSubmission.Global.Binding.jumpDest 1903 (by rfl)

theorem jumpDest4839 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2660 = true :=
  CycleSubmission.Global.Binding.jumpDest 2056 (by rfl)

/-- The appended four-limb loop head. -/
theorem jumpDestHead4 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10692 = true :=
  CycleSubmission.Global.Binding.jumpDest 8211 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3071 = true :=
  CycleSubmission.Global.Binding.jumpDest 2346 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3077 = true :=
  CycleSubmission.Global.Binding.jumpDest 2350 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3069 = true :=
  CycleSubmission.Global.Binding.jumpDest 2344 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3047 = true :=
  CycleSubmission.Global.Binding.jumpDest 2331 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3053 = true :=
  CycleSubmission.Global.Binding.jumpDest 2337 (by rfl)

theorem jumpDest5444 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3914 = true :=
  CycleSubmission.Global.Binding.jumpDest 2968 (by rfl)

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
  [opAt 2046 (.Dup dA15),
   opAt 2047 .SHR,
   opAt 2048 (.Dup dA13),
   pushAt 2049 2 2008,
   opAt 2050 .MUL,
   pushAt 2051 2 18724,
   opAt 2052 .SUB,
   opAt 2053 (.Swap sA0),
   opAt 2054 (.Dup dA1),
   opAt 2055 .JUMP]

/-- The cleanup tail (pcs 3866-3887): sixteen `POP`s drop all riding slots but the last,
then `PUSH2 0989 ADD JUMP` jumps to `2441 + z`, where `z` is that last slot: `0` from `E5`
(the exponent dispatcher at 2441) and `28` after the E3 phase switch (`e3go` at 2471). -/
def blk5444 :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 2968 .JUMPDEST,
   opAt 2969 .POP,
   opAt 2970 .POP,
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
   pushAt 2985 2 2284,
   opAt 2986 .ADD,
   opAt 2987 .JUMP]

end CycleSubmission.Global.Fast

namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
