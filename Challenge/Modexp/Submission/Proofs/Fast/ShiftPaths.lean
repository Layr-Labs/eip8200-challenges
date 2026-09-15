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
  [opAt 1939 .JUMPDEST,
   opAt 1940 (.Dup ⟨0, by decide⟩),
   opAt 1941 (.Dup ⟨3, by decide⟩),
   opAt 1942 .EQ,
   pushAt 1943 0 0,
   opAt 1944 .MLOAD,
   pushAt 1945 1 255,
   opAt 1946 .SHR,
   opAt 1947 .AND,
   opAt 1948 .ISZERO,
   pushAt 1949 2 2634,
   opAt 1950 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1951 (.Dup ⟨0, by decide⟩),
   pushAt 1952 1 96,
   pushAt 1953 2 2112,
   opAt 1954 .CALLDATACOPY,
   pushAt 1955 0 0,
   pushAt 1956 2 2080,
   opAt 1957 .MSTORE,
   pushAt 1958 2 2651,
   pushAt 1959 2 4284,
   opAt 1960 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1961 .JUMPDEST,
   pushAt 1962 1 1,
   pushAt 1963 2 1024,
   opAt 1964 .MSTORE,
   pushAt 1965 2 771,
   pushAt 1966 2 1024,
   pushAt 1967 2 1539,
   opAt 1968 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1974 1 1,
   pushAt 1975 2 2752,
   opAt 1976 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1998 .POP,
   opAt 1999 .POP,
   pushAt 2000 0 0,
   opAt 2001 .MLOAD,
   opAt 2002 (.Dup ⟨0, by decide⟩),
   pushAt 2003 0 0,
   opAt 2004 .SUB,
   opAt 2005 (.Dup ⟨1, by decide⟩),
   opAt 2006 .AND,
   opAt 2007 (.Dup ⟨0, by decide⟩),
   pushAt 2008 2 1536,
   opAt 2009 .MSTORE,
   opAt 2010 (.Dup ⟨0, by decide⟩),
   opAt 2011 (.Dup ⟨2, by decide⟩),
   opAt 2012 .DIV,
   opAt 2013 (.Dup ⟨0, by decide⟩),
   pushAt 2014 2 1568,
   opAt 2015 .MSTORE,
   opAt 2016 (.Dup ⟨1, by decide⟩),
   opAt 2017 (.Dup ⟨0, by decide⟩),
   pushAt 2018 0 0,
   opAt 2019 .SUB,
   opAt 2020 .DIV,
   pushAt 2021 1 1,
   opAt 2022 .ADD,
   pushAt 2023 2 1600,
   opAt 2024 .MSTORE,
   opAt 2025 (.Dup ⟨0, by decide⟩),
   opAt 2026 (.Dup ⟨0, by decide⟩),
   pushAt 2027 0 0,
   opAt 2028 .SUB,
   opAt 2029 .MOD,
   pushAt 2030 2 1632,
   opAt 2031 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2032 (.Dup ⟨0, by decide⟩),
   pushAt 2033 1 3,
   opAt 2034 .MUL,
   pushAt 2035 1 2,
   opAt 2036 .XOR,
   opAt 2037 (.Dup ⟨0, by decide⟩),
   opAt 2038 (.Dup ⟨2, by decide⟩),
   opAt 2039 .MUL,
   pushAt 2040 1 2,
   opAt 2041 .SUB,
   opAt 2042 .MUL,
   opAt 2043 (.Dup ⟨0, by decide⟩),
   opAt 2044 (.Dup ⟨2, by decide⟩),
   opAt 2045 .MUL,
   pushAt 2046 1 2,
   opAt 2047 .SUB,
   opAt 2048 .MUL,
   opAt 2049 (.Dup ⟨0, by decide⟩),
   opAt 2050 (.Dup ⟨2, by decide⟩),
   opAt 2051 .MUL,
   pushAt 2052 1 2,
   opAt 2053 .SUB,
   opAt 2054 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2055 (.Dup ⟨0, by decide⟩),
   opAt 2056 (.Dup ⟨2, by decide⟩),
   opAt 2057 .MUL,
   pushAt 2058 1 2,
   opAt 2059 .SUB,
   opAt 2060 .MUL,
   opAt 2061 (.Dup ⟨0, by decide⟩),
   opAt 2062 (.Dup ⟨2, by decide⟩),
   opAt 2063 .MUL,
   pushAt 2064 1 2,
   opAt 2065 .SUB,
   opAt 2066 .MUL,
   opAt 2067 (.Dup ⟨0, by decide⟩),
   opAt 2068 (.Dup ⟨2, by decide⟩),
   opAt 2069 .MUL,
   pushAt 2070 1 2,
   opAt 2071 .SUB,
   opAt 2072 .MUL,
   pushAt 2073 2 1664,
   opAt 2074 .MSTORE,
   opAt 2075 .POP,
   opAt 2076 .POP,
   opAt 2077 .POP,
   opAt 2078 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2110 .JUMPDEST,
   opAt 2111 (.Dup ⟨0, by decide⟩),
   opAt 2112 .ISZERO,
   pushAt 2113 2 3300,
   opAt 2114 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2115 (.Dup ⟨1, by decide⟩),
   pushAt 2116 2 2112,
   pushAt 2117 2 2080,
   opAt 2118 .MCOPY,
   pushAt 2119 0 0,
   pushAt 2120 2 2784,
   opAt 2121 .MLOAD,
   opAt 2122 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2123 2 2080,
   opAt 2124 .MLOAD,
   pushAt 2125 2 1536,
   opAt 2126 .MLOAD,
   opAt 2127 (.Dup ⟨1, by decide⟩),
   opAt 2128 .DIV,
   opAt 2129 (.Swap ⟨0, by decide⟩),
   pushAt 2130 2 1600,
   opAt 2131 .MLOAD,
   opAt 2132 .MUL,
   pushAt 2133 2 1536,
   opAt 2134 .MLOAD,
   pushAt 2135 2 2112,
   opAt 2136 .MLOAD,
   opAt 2137 .DIV,
   opAt 2138 .ADD,
   pushAt 2139 2 1568,
   opAt 2140 .MLOAD,
   opAt 2141 (.Dup ⟨0, by decide⟩),
   pushAt 2142 2 1632,
   opAt 2143 .MLOAD,
   opAt 2144 (.Dup ⟨4, by decide⟩),
   opAt 2145 .MULMOD,
   opAt 2146 (.Dup ⟨2, by decide⟩),
   opAt 2147 .ADDMOD,
   opAt 2148 (.Swap ⟨0, by decide⟩),
   opAt 2149 .SUB,
   pushAt 2150 2 1664,
   opAt 2151 .MLOAD,
   opAt 2152 .MUL,
   opAt 2153 (.Dup ⟨0, by decide⟩),
   pushAt 2154 0 0,
   opAt 2155 .MLOAD,
   opAt 2156 .MUL,
   pushAt 2157 2 2112,
   opAt 2158 .MLOAD,
   opAt 2159 .SUB,
   pushAt 2160 1 32,
   opAt 2161 .MLOAD,
   pushAt 2162 1 128,
   opAt 2163 .SHR,
   opAt 2164 (.Dup ⟨2, by decide⟩),
   pushAt 2165 1 128,
   opAt 2166 .SHR,
   opAt 2167 .MUL,
   opAt 2168 .GT,
   opAt 2169 (.Swap ⟨0, by decide⟩),
   opAt 2170 .SUB,
   opAt 2171 (.Swap ⟨0, by decide⟩),
   pushAt 2172 2 1568,
   opAt 2173 .MLOAD,
   opAt 2174 .GT,
   opAt 2175 .ISZERO,
   pushAt 2176 0 0,
   opAt 2177 .SUB,
   opAt 2178 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2179 0 0,
   pushAt 2180 1 31,
   opAt 2181 .NOT,
   pushAt 2182 0 0,
   opAt 2183 .NOT,
   pushAt 2184 2 2784,
   opAt 2185 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2189 .JUMPDEST,
   pushAt 2190 2 832,
   opAt 2191 (.Dup ⟨1, by decide⟩),
   opAt 2192 .SUB,
   opAt 2193 .MLOAD,
   opAt 2194 (.Dup ⟨2, by decide⟩),
   opAt 2195 (.Dup ⟨6, by decide⟩),
   opAt 2196 (.Dup ⟨2, by decide⟩),
   opAt 2197 .MUL,
   opAt 2198 (.Swap ⟨1, by decide⟩),
   opAt 2199 (.Dup ⟨7, by decide⟩),
   opAt 2200 .MULMOD,
   opAt 2201 (.Dup ⟨1, by decide⟩),
   opAt 2202 (.Dup ⟨1, by decide⟩),
   opAt 2203 .LT,
   opAt 2204 .SUB,
   opAt 2205 (.Dup ⟨5, by decide⟩),
   opAt 2206 (.Dup ⟨2, by decide⟩),
   opAt 2207 .ADD,
   opAt 2208 (.Dup ⟨0, by decide⟩),
   opAt 2209 (.Swap ⟨6, by decide⟩),
   opAt 2210 .GT,
   opAt 2211 .SUB,
   opAt 2212 .SUB,
   opAt 2213 (.Dup ⟨4, by decide⟩),
   opAt 2214 (.Dup ⟨2, by decide⟩),
   opAt 2215 .MLOAD,
   opAt 2216 .ADD,
   opAt 2217 (.Dup ⟨0, by decide⟩),
   opAt 2218 (.Swap ⟨5, by decide⟩),
   opAt 2219 .GT,
   opAt 2220 .ADD,
   opAt 2221 (.Swap ⟨3, by decide⟩),
   opAt 2222 (.Dup ⟨1, by decide⟩),
   opAt 2223 .MSTORE,
   opAt 2224 (.Dup ⟨2, by decide⟩),
   opAt 2225 .ADD,
   pushAt 2337 2 2080,
   opAt 2338 (.Dup ⟨1, by decide⟩),
   opAt 2339 .GT,
   pushAt 2340 2 2951,
   opAt 2341 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2342 .POP,
   opAt 2343 .POP,
   opAt 2344 .POP,
   pushAt 2345 2 2080,
   opAt 2346 .MLOAD,
   opAt 2347 (.Dup ⟨1, by decide⟩),
   opAt 2348 .ADD,
   opAt 2349 (.Dup ⟨0, by decide⟩),
   opAt 2350 (.Swap ⟨1, by decide⟩),
   opAt 2351 .GT,
   opAt 2352 (.Dup ⟨1, by decide⟩),
   opAt 2353 (.Dup ⟨3, by decide⟩),
   opAt 2354 .GT,
   opAt 2355 .GT,
   opAt 2356 (.Swap ⟨1, by decide⟩),
   opAt 2357 (.Swap ⟨0, by decide⟩),
   opAt 2358 .SUB,
   opAt 2359 (.Dup ⟨0, by decide⟩),
   pushAt 2360 2 2080,
   opAt 2361 .MSTORE,
   opAt 2362 (.Dup ⟨1, by decide⟩),
   opAt 2363 .OR,
   pushAt 2364 2 3156,
   opAt 2365 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2372 .JUMPDEST,
   opAt 2373 .ISZERO,
   pushAt 2374 2 3241,
   opAt 2375 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2376 .JUMPDEST,
   pushAt 2377 0 0,
   pushAt 2378 2 2784,
   opAt 2379 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2380 .JUMPDEST,
   opAt 2381 (.Dup ⟨0, by decide⟩),
   opAt 2382 .MLOAD,
   pushAt 2383 3 2112,
   opAt 2384 (.Dup ⟨2, by decide⟩),
   opAt 2385 .SUB,
   opAt 2386 .MLOAD,
   opAt 2387 (.Dup ⟨1, by decide⟩),
   opAt 2388 .ADD,
   opAt 2389 (.Swap ⟨0, by decide⟩),
   opAt 2390 (.Dup ⟨1, by decide⟩),
   opAt 2391 .LT,
   opAt 2392 (.Swap ⟨0, by decide⟩),
   opAt 2393 (.Dup ⟨3, by decide⟩),
   opAt 2394 .ADD,
   opAt 2395 (.Swap ⟨2, by decide⟩),
   opAt 2396 (.Dup ⟨3, by decide⟩),
   opAt 2397 .LT,
   opAt 2398 .OR,
   opAt 2399 (.Swap ⟨1, by decide⟩),
   opAt 2400 (.Dup ⟨1, by decide⟩),
   opAt 2401 .MSTORE,
   pushAt 2402 1 31,
   opAt 2403 .NOT,
   opAt 2404 .ADD,
   pushAt 2405 2 2111,
   opAt 2406 (.Dup ⟨1, by decide⟩),
   opAt 2407 .GT,
   pushAt 2408 2 3168,
   opAt 2409 .JUMPI,
   opAt 2410 .JUMPDEST,
   opAt 2411 .JUMPDEST,
   opAt 2412 .JUMPDEST,
   opAt 2413 .JUMPDEST,
   opAt 2414 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2415 .POP,
   pushAt 2416 2 2080,
   opAt 2417 .MLOAD,
   opAt 2418 (.Dup ⟨1, by decide⟩),
   opAt 2419 .ADD,
   opAt 2420 (.Dup ⟨0, by decide⟩),
   pushAt 2421 2 2080,
   opAt 2422 .MSTORE,
   opAt 2423 .LT,
   opAt 2424 .ISZERO,
   pushAt 2425 2 3162,
   opAt 2426 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2427 .JUMPDEST,
   pushAt 2428 2 2080,
   opAt 2429 .MLOAD,
   opAt 2430 (.Dup ⟨0, by decide⟩),
   opAt 2431 .ISZERO,
   pushAt 2432 2 3146,
   opAt 2433 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2427 .JUMPDEST,
   pushAt 2428 2 2080,
   opAt 2429 .MLOAD,
   opAt 2430 (.Dup ⟨0, by decide⟩),
   opAt 2431 .ISZERO,
   pushAt 2432 2 3146,
   opAt 2433 .JUMPI,
   opAt 2434 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2435 .JUMPDEST,
   pushAt 2436 0 0,
   pushAt 2437 2 2784,
   opAt 2438 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2439 .JUMPDEST,
   opAt 2440 (.Dup ⟨0, by decide⟩),
   opAt 2441 .MLOAD,
   pushAt 2442 2 2112,
   opAt 2443 (.Dup ⟨2, by decide⟩),
   opAt 2444 .SUB,
   opAt 2445 .MLOAD,
   opAt 2446 (.Dup ⟨1, by decide⟩),
   opAt 2447 (.Dup ⟨1, by decide⟩),
   opAt 2448 .GT,
   opAt 2449 (.Swap ⟨1, by decide⟩),
   opAt 2450 .SUB,
   opAt 2451 (.Dup ⟨3, by decide⟩),
   opAt 2452 (.Dup ⟨1, by decide⟩),
   opAt 2453 .LT,
   opAt 2454 (.Swap ⟨0, by decide⟩),
   opAt 2455 (.Dup ⟨4, by decide⟩),
   opAt 2456 (.Swap ⟨0, by decide⟩),
   opAt 2457 .SUB,
   opAt 2458 (.Dup ⟨3, by decide⟩),
   opAt 2459 .MSTORE,
   opAt 2460 .OR,
   opAt 2461 (.Swap ⟨1, by decide⟩),
   opAt 2462 .POP,
   pushAt 2463 1 31,
   opAt 2464 .NOT,
   opAt 2465 .ADD,
   pushAt 2466 2 2111,
   opAt 2467 (.Dup ⟨1, by decide⟩),
   opAt 2468 .GT,
   pushAt 2469 2 3247,
   opAt 2470 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2471 .POP,
   pushAt 2472 2 2080,
   opAt 2473 .MLOAD,
   opAt 2474 .SUB,
   pushAt 2475 2 2080,
   opAt 2476 .MSTORE,
   pushAt 2477 2 3229,
   opAt 2478 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2366 .JUMPDEST,
   opAt 2367 .NOT,
   opAt 2368 .ADD,
   pushAt 2369 2 2836,
   pushAt 2370 2 4284,
   opAt 2371 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2499 (.Dup ⟨0, by decide⟩),
   pushAt 2500 2 2112,
   pushAt 2501 2 512,
   opAt 2502 .MCOPY,
   opAt 2503 (.Dup ⟨0, by decide⟩),
   pushAt 2504 2 1280,
   pushAt 2505 2 1024,
   opAt 2506 .MCOPY,
   pushAt 2507 2 2443,
   opAt 2508 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2600 = true :=
  Artifact.isValidJumpDest_index 1939 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2634 = true :=
  Artifact.isValidJumpDest_index 1961 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2651 = true :=
  Artifact.isValidJumpDest_index 1969 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2666 = true :=
  Artifact.isValidJumpDest_index 1977 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2836 = true :=
  Artifact.isValidJumpDest_index 2110 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2951 = true :=
  Artifact.isValidJumpDest_index 2189 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3162 = true :=
  Artifact.isValidJumpDest_index 2376 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3168 = true :=
  Artifact.isValidJumpDest_index 2380 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3229 = true :=
  Artifact.isValidJumpDest_index 2427 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3247 = true :=
  Artifact.isValidJumpDest_index 2439 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2372 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3241 = true :=
  Artifact.isValidJumpDest_index 2435 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3146 = true :=
  Artifact.isValidJumpDest_index 2366 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3300 = true :=
  Artifact.isValidJumpDest_index 2479 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
