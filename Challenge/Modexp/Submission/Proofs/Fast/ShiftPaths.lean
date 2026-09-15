import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths for the appended shift-reduce base conversion (generated). -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Located block of the selected shift-reduce program. -/
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1938 .JUMPDEST,
   opAt 1939 (.Dup ⟨0, by decide⟩),
   opAt 1940 (.Dup ⟨3, by decide⟩),
   opAt 1941 .EQ,
   pushAt 1942 0 0,
   opAt 1943 .MLOAD,
   pushAt 1944 1 255,
   opAt 1945 .SHR,
   opAt 1946 .AND,
   opAt 1947 .ISZERO,
   pushAt 1948 2 2634,
   opAt 1949 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1950 (.Dup ⟨0, by decide⟩),
   pushAt 1951 1 96,
   pushAt 1952 2 2112,
   opAt 1953 .CALLDATACOPY,
   pushAt 1954 0 0,
   pushAt 1955 2 2080,
   opAt 1956 .MSTORE,
   pushAt 1957 2 2651,
   pushAt 1958 2 4284,
   opAt 1959 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1960 .JUMPDEST,
   pushAt 1961 1 1,
   pushAt 1962 2 1024,
   opAt 1963 .MSTORE,
   pushAt 1964 2 771,
   pushAt 1965 2 1024,
   pushAt 1966 2 1539,
   opAt 1967 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1973 1 1,
   pushAt 1974 2 2752,
   opAt 1975 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1997 .POP,
   opAt 1998 .POP,
   pushAt 1999 0 0,
   opAt 2000 .MLOAD,
   opAt 2001 (.Dup ⟨0, by decide⟩),
   pushAt 2002 0 0,
   opAt 2003 .SUB,
   opAt 2004 (.Dup ⟨1, by decide⟩),
   opAt 2005 .AND,
   opAt 2006 (.Dup ⟨0, by decide⟩),
   pushAt 2007 2 1536,
   opAt 2008 .MSTORE,
   opAt 2009 (.Dup ⟨0, by decide⟩),
   opAt 2010 (.Dup ⟨2, by decide⟩),
   opAt 2011 .DIV,
   opAt 2012 (.Dup ⟨0, by decide⟩),
   pushAt 2013 2 1568,
   opAt 2014 .MSTORE,
   opAt 2015 (.Dup ⟨1, by decide⟩),
   opAt 2016 (.Dup ⟨0, by decide⟩),
   pushAt 2017 0 0,
   opAt 2018 .SUB,
   opAt 2019 .DIV,
   pushAt 2020 1 1,
   opAt 2021 .ADD,
   pushAt 2022 2 1600,
   opAt 2023 .MSTORE,
   opAt 2024 (.Dup ⟨0, by decide⟩),
   opAt 2025 (.Dup ⟨0, by decide⟩),
   pushAt 2026 0 0,
   opAt 2027 .SUB,
   opAt 2028 .MOD,
   pushAt 2029 2 1632,
   opAt 2030 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2031 (.Dup ⟨0, by decide⟩),
   pushAt 2032 1 3,
   opAt 2033 .MUL,
   pushAt 2034 1 2,
   opAt 2035 .XOR,
   opAt 2036 (.Dup ⟨0, by decide⟩),
   opAt 2037 (.Dup ⟨2, by decide⟩),
   opAt 2038 .MUL,
   pushAt 2039 1 2,
   opAt 2040 .SUB,
   opAt 2041 .MUL,
   opAt 2042 (.Dup ⟨0, by decide⟩),
   opAt 2043 (.Dup ⟨2, by decide⟩),
   opAt 2044 .MUL,
   pushAt 2045 1 2,
   opAt 2046 .SUB,
   opAt 2047 .MUL,
   opAt 2048 (.Dup ⟨0, by decide⟩),
   opAt 2049 (.Dup ⟨2, by decide⟩),
   opAt 2050 .MUL,
   pushAt 2051 1 2,
   opAt 2052 .SUB,
   opAt 2053 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2054 (.Dup ⟨0, by decide⟩),
   opAt 2055 (.Dup ⟨2, by decide⟩),
   opAt 2056 .MUL,
   pushAt 2057 1 2,
   opAt 2058 .SUB,
   opAt 2059 .MUL,
   opAt 2060 (.Dup ⟨0, by decide⟩),
   opAt 2061 (.Dup ⟨2, by decide⟩),
   opAt 2062 .MUL,
   pushAt 2063 1 2,
   opAt 2064 .SUB,
   opAt 2065 .MUL,
   opAt 2066 (.Dup ⟨0, by decide⟩),
   opAt 2067 (.Dup ⟨2, by decide⟩),
   opAt 2068 .MUL,
   pushAt 2069 1 2,
   opAt 2070 .SUB,
   opAt 2071 .MUL,
   pushAt 2072 2 1664,
   opAt 2073 .MSTORE,
   opAt 2074 .POP,
   opAt 2075 .POP,
   opAt 2076 .POP,
   opAt 2077 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2109 .JUMPDEST,
   opAt 2110 (.Dup ⟨0, by decide⟩),
   opAt 2111 .ISZERO,
   pushAt 2112 2 3300,
   opAt 2113 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2114 (.Dup ⟨1, by decide⟩),
   pushAt 2115 2 2112,
   pushAt 2116 2 2080,
   opAt 2117 .MCOPY,
   pushAt 2118 0 0,
   pushAt 2119 2 2784,
   opAt 2120 .MLOAD,
   opAt 2121 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2122 2 2080,
   opAt 2123 .MLOAD,
   pushAt 2124 2 1536,
   opAt 2125 .MLOAD,
   opAt 2126 (.Dup ⟨1, by decide⟩),
   opAt 2127 .DIV,
   opAt 2128 (.Swap ⟨0, by decide⟩),
   pushAt 2129 2 1600,
   opAt 2130 .MLOAD,
   opAt 2131 .MUL,
   pushAt 2132 2 1536,
   opAt 2133 .MLOAD,
   pushAt 2134 2 2112,
   opAt 2135 .MLOAD,
   opAt 2136 .DIV,
   opAt 2137 .ADD,
   pushAt 2138 2 1568,
   opAt 2139 .MLOAD,
   opAt 2140 (.Dup ⟨0, by decide⟩),
   pushAt 2141 2 1632,
   opAt 2142 .MLOAD,
   opAt 2143 (.Dup ⟨4, by decide⟩),
   opAt 2144 .MULMOD,
   opAt 2145 (.Dup ⟨2, by decide⟩),
   opAt 2146 .ADDMOD,
   opAt 2147 (.Swap ⟨0, by decide⟩),
   opAt 2148 .SUB,
   pushAt 2149 2 1664,
   opAt 2150 .MLOAD,
   opAt 2151 .MUL,
   opAt 2152 (.Dup ⟨0, by decide⟩),
   pushAt 2153 0 0,
   opAt 2154 .MLOAD,
   opAt 2155 .MUL,
   pushAt 2156 2 2112,
   opAt 2157 .MLOAD,
   opAt 2158 .SUB,
   pushAt 2159 1 32,
   opAt 2160 .MLOAD,
   pushAt 2161 1 128,
   opAt 2162 .SHR,
   opAt 2163 (.Dup ⟨2, by decide⟩),
   pushAt 2164 1 128,
   opAt 2165 .SHR,
   opAt 2166 .MUL,
   opAt 2167 .GT,
   opAt 2168 (.Swap ⟨0, by decide⟩),
   opAt 2169 .SUB,
   opAt 2170 (.Swap ⟨0, by decide⟩),
   pushAt 2171 2 1568,
   opAt 2172 .MLOAD,
   opAt 2173 .GT,
   opAt 2174 .ISZERO,
   pushAt 2175 0 0,
   opAt 2176 .SUB,
   opAt 2177 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2178 0 0,
   pushAt 2179 1 31,
   opAt 2180 .NOT,
   pushAt 2181 0 0,
   opAt 2182 .NOT,
   pushAt 2183 2 2784,
   opAt 2184 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2188 .JUMPDEST,
   pushAt 2189 2 832,
   opAt 2190 (.Dup ⟨1, by decide⟩),
   opAt 2191 .SUB,
   opAt 2192 .MLOAD,
   opAt 2193 (.Dup ⟨2, by decide⟩),
   opAt 2194 (.Dup ⟨6, by decide⟩),
   opAt 2195 (.Dup ⟨2, by decide⟩),
   opAt 2196 .MUL,
   opAt 2197 (.Swap ⟨1, by decide⟩),
   opAt 2198 (.Dup ⟨7, by decide⟩),
   opAt 2199 .MULMOD,
   opAt 2200 (.Dup ⟨1, by decide⟩),
   opAt 2201 (.Dup ⟨1, by decide⟩),
   opAt 2202 .LT,
   opAt 2203 .SUB,
   opAt 2204 (.Dup ⟨5, by decide⟩),
   opAt 2205 (.Dup ⟨2, by decide⟩),
   opAt 2206 .ADD,
   opAt 2207 (.Dup ⟨0, by decide⟩),
   opAt 2208 (.Swap ⟨6, by decide⟩),
   opAt 2209 .GT,
   opAt 2210 .SUB,
   opAt 2211 .SUB,
   opAt 2212 (.Dup ⟨4, by decide⟩),
   opAt 2213 (.Dup ⟨2, by decide⟩),
   opAt 2214 .MLOAD,
   opAt 2215 .ADD,
   opAt 2216 (.Dup ⟨0, by decide⟩),
   opAt 2217 (.Swap ⟨5, by decide⟩),
   opAt 2218 .GT,
   opAt 2219 .ADD,
   opAt 2220 (.Swap ⟨3, by decide⟩),
   opAt 2221 (.Dup ⟨1, by decide⟩),
   opAt 2222 .MSTORE,
   opAt 2223 (.Dup ⟨2, by decide⟩),
   opAt 2224 .ADD,
   pushAt 2336 2 2080,
   opAt 2337 (.Dup ⟨1, by decide⟩),
   opAt 2338 .GT,
   pushAt 2339 2 2951,
   opAt 2340 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2341 .POP,
   opAt 2342 .POP,
   opAt 2343 .POP,
   pushAt 2344 2 2080,
   opAt 2345 .MLOAD,
   opAt 2346 (.Dup ⟨1, by decide⟩),
   opAt 2347 .ADD,
   opAt 2348 (.Dup ⟨0, by decide⟩),
   opAt 2349 (.Swap ⟨1, by decide⟩),
   opAt 2350 .GT,
   opAt 2351 (.Dup ⟨1, by decide⟩),
   opAt 2352 (.Dup ⟨3, by decide⟩),
   opAt 2353 .GT,
   opAt 2354 .GT,
   opAt 2355 (.Swap ⟨1, by decide⟩),
   opAt 2356 (.Swap ⟨0, by decide⟩),
   opAt 2357 .SUB,
   opAt 2358 (.Dup ⟨0, by decide⟩),
   pushAt 2359 2 2080,
   opAt 2360 .MSTORE,
   opAt 2361 (.Dup ⟨1, by decide⟩),
   opAt 2362 .OR,
   pushAt 2363 2 3156,
   opAt 2364 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2371 .JUMPDEST,
   opAt 2372 .ISZERO,
   pushAt 2373 2 3241,
   opAt 2374 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2375 .JUMPDEST,
   pushAt 2376 0 0,
   pushAt 2377 2 2784,
   opAt 2378 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2379 .JUMPDEST,
   opAt 2380 (.Dup ⟨0, by decide⟩),
   opAt 2381 .MLOAD,
   pushAt 2382 3 2112,
   opAt 2383 (.Dup ⟨2, by decide⟩),
   opAt 2384 .SUB,
   opAt 2385 .MLOAD,
   opAt 2386 (.Dup ⟨1, by decide⟩),
   opAt 2387 .ADD,
   opAt 2388 (.Swap ⟨0, by decide⟩),
   opAt 2389 (.Dup ⟨1, by decide⟩),
   opAt 2390 .LT,
   opAt 2391 (.Swap ⟨0, by decide⟩),
   opAt 2392 (.Dup ⟨3, by decide⟩),
   opAt 2393 .ADD,
   opAt 2394 (.Swap ⟨2, by decide⟩),
   opAt 2395 (.Dup ⟨3, by decide⟩),
   opAt 2396 .LT,
   opAt 2397 .OR,
   opAt 2398 (.Swap ⟨1, by decide⟩),
   opAt 2399 (.Dup ⟨1, by decide⟩),
   opAt 2400 .MSTORE,
   pushAt 2401 1 31,
   opAt 2402 .NOT,
   opAt 2403 .ADD,
   pushAt 2404 2 2111,
   opAt 2405 (.Dup ⟨1, by decide⟩),
   opAt 2406 .GT,
   pushAt 2407 2 3168,
   opAt 2408 .JUMPI,
   opAt 2409 .JUMPDEST,
   opAt 2410 .JUMPDEST,
   opAt 2411 .JUMPDEST,
   opAt 2412 .JUMPDEST,
   opAt 2413 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2414 .POP,
   pushAt 2415 2 2080,
   opAt 2416 .MLOAD,
   opAt 2417 (.Dup ⟨1, by decide⟩),
   opAt 2418 .ADD,
   opAt 2419 (.Dup ⟨0, by decide⟩),
   pushAt 2420 2 2080,
   opAt 2421 .MSTORE,
   opAt 2422 .LT,
   opAt 2423 .ISZERO,
   pushAt 2424 2 3162,
   opAt 2425 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2426 .JUMPDEST,
   pushAt 2427 2 2080,
   opAt 2428 .MLOAD,
   opAt 2429 (.Dup ⟨0, by decide⟩),
   opAt 2430 .ISZERO,
   pushAt 2431 2 3146,
   opAt 2432 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2426 .JUMPDEST,
   pushAt 2427 2 2080,
   opAt 2428 .MLOAD,
   opAt 2429 (.Dup ⟨0, by decide⟩),
   opAt 2430 .ISZERO,
   pushAt 2431 2 3146,
   opAt 2432 .JUMPI,
   opAt 2433 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2434 .JUMPDEST,
   pushAt 2435 0 0,
   pushAt 2436 2 2784,
   opAt 2437 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2438 .JUMPDEST,
   opAt 2439 (.Dup ⟨0, by decide⟩),
   opAt 2440 .MLOAD,
   pushAt 2441 2 2112,
   opAt 2442 (.Dup ⟨2, by decide⟩),
   opAt 2443 .SUB,
   opAt 2444 .MLOAD,
   opAt 2445 (.Dup ⟨1, by decide⟩),
   opAt 2446 (.Dup ⟨1, by decide⟩),
   opAt 2447 .GT,
   opAt 2448 (.Swap ⟨1, by decide⟩),
   opAt 2449 .SUB,
   opAt 2450 (.Dup ⟨3, by decide⟩),
   opAt 2451 (.Dup ⟨1, by decide⟩),
   opAt 2452 .LT,
   opAt 2453 (.Swap ⟨0, by decide⟩),
   opAt 2454 (.Dup ⟨4, by decide⟩),
   opAt 2455 (.Swap ⟨0, by decide⟩),
   opAt 2456 .SUB,
   opAt 2457 (.Dup ⟨3, by decide⟩),
   opAt 2458 .MSTORE,
   opAt 2459 .OR,
   opAt 2460 (.Swap ⟨1, by decide⟩),
   opAt 2461 .POP,
   pushAt 2462 1 31,
   opAt 2463 .NOT,
   opAt 2464 .ADD,
   pushAt 2465 2 2111,
   opAt 2466 (.Dup ⟨1, by decide⟩),
   opAt 2467 .GT,
   pushAt 2468 2 3247,
   opAt 2469 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2470 .POP,
   pushAt 2471 2 2080,
   opAt 2472 .MLOAD,
   opAt 2473 .SUB,
   pushAt 2474 2 2080,
   opAt 2475 .MSTORE,
   pushAt 2476 2 3229,
   opAt 2477 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2365 .JUMPDEST,
   opAt 2366 .NOT,
   opAt 2367 .ADD,
   pushAt 2368 2 2836,
   pushAt 2369 2 4284,
   opAt 2370 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2498 (.Dup ⟨0, by decide⟩),
   pushAt 2499 2 2112,
   pushAt 2500 2 512,
   opAt 2501 .MCOPY,
   opAt 2502 (.Dup ⟨0, by decide⟩),
   pushAt 2503 2 1280,
   pushAt 2504 2 1024,
   opAt 2505 .MCOPY,
   pushAt 2506 2 2443,
   opAt 2507 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2600 = true :=
  Artifact.isValidJumpDest_index 1938 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2634 = true :=
  Artifact.isValidJumpDest_index 1960 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2651 = true :=
  Artifact.isValidJumpDest_index 1968 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2666 = true :=
  Artifact.isValidJumpDest_index 1976 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2836 = true :=
  Artifact.isValidJumpDest_index 2109 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2951 = true :=
  Artifact.isValidJumpDest_index 2188 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3162 = true :=
  Artifact.isValidJumpDest_index 2375 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3168 = true :=
  Artifact.isValidJumpDest_index 2379 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3229 = true :=
  Artifact.isValidJumpDest_index 2426 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3247 = true :=
  Artifact.isValidJumpDest_index 2438 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2371 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3241 = true :=
  Artifact.isValidJumpDest_index 2434 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3146 = true :=
  Artifact.isValidJumpDest_index 2365 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3300 = true :=
  Artifact.isValidJumpDest_index 2478 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
