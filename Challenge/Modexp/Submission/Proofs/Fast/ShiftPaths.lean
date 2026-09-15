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
  [opAt 1940 .JUMPDEST,
   opAt 1941 (.Dup ⟨0, by decide⟩),
   opAt 1942 (.Dup ⟨3, by decide⟩),
   opAt 1943 .EQ,
   pushAt 1944 0 0,
   opAt 1945 .MLOAD,
   pushAt 1946 1 255,
   opAt 1947 .SHR,
   opAt 1948 .AND,
   opAt 1949 .ISZERO,
   pushAt 1950 2 2634,
   opAt 1951 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1952 (.Dup ⟨0, by decide⟩),
   pushAt 1953 1 96,
   pushAt 1954 2 2112,
   opAt 1955 .CALLDATACOPY,
   pushAt 1956 0 0,
   pushAt 1957 2 2080,
   opAt 1958 .MSTORE,
   pushAt 1959 2 2651,
   pushAt 1960 2 4284,
   opAt 1961 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1962 .JUMPDEST,
   pushAt 1963 1 1,
   pushAt 1964 2 1024,
   opAt 1965 .MSTORE,
   pushAt 1966 2 771,
   pushAt 1967 2 1024,
   pushAt 1968 2 1539,
   opAt 1969 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1975 1 1,
   pushAt 1976 2 2752,
   opAt 1977 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1999 .POP,
   opAt 2000 .POP,
   pushAt 2001 0 0,
   opAt 2002 .MLOAD,
   opAt 2003 (.Dup ⟨0, by decide⟩),
   pushAt 2004 0 0,
   opAt 2005 .SUB,
   opAt 2006 (.Dup ⟨1, by decide⟩),
   opAt 2007 .AND,
   opAt 2008 (.Dup ⟨0, by decide⟩),
   pushAt 2009 2 1536,
   opAt 2010 .MSTORE,
   opAt 2011 (.Dup ⟨0, by decide⟩),
   opAt 2012 (.Dup ⟨2, by decide⟩),
   opAt 2013 .DIV,
   opAt 2014 (.Dup ⟨0, by decide⟩),
   pushAt 2015 2 1568,
   opAt 2016 .MSTORE,
   opAt 2017 (.Dup ⟨1, by decide⟩),
   opAt 2018 (.Dup ⟨0, by decide⟩),
   pushAt 2019 0 0,
   opAt 2020 .SUB,
   opAt 2021 .DIV,
   pushAt 2022 1 1,
   opAt 2023 .ADD,
   pushAt 2024 2 1600,
   opAt 2025 .MSTORE,
   opAt 2026 (.Dup ⟨0, by decide⟩),
   opAt 2027 (.Dup ⟨0, by decide⟩),
   pushAt 2028 0 0,
   opAt 2029 .SUB,
   opAt 2030 .MOD,
   pushAt 2031 2 1632,
   opAt 2032 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2033 (.Dup ⟨0, by decide⟩),
   pushAt 2034 1 3,
   opAt 2035 .MUL,
   pushAt 2036 1 2,
   opAt 2037 .XOR,
   opAt 2038 (.Dup ⟨0, by decide⟩),
   opAt 2039 (.Dup ⟨2, by decide⟩),
   opAt 2040 .MUL,
   pushAt 2041 1 2,
   opAt 2042 .SUB,
   opAt 2043 .MUL,
   opAt 2044 (.Dup ⟨0, by decide⟩),
   opAt 2045 (.Dup ⟨2, by decide⟩),
   opAt 2046 .MUL,
   pushAt 2047 1 2,
   opAt 2048 .SUB,
   opAt 2049 .MUL,
   opAt 2050 (.Dup ⟨0, by decide⟩),
   opAt 2051 (.Dup ⟨2, by decide⟩),
   opAt 2052 .MUL,
   pushAt 2053 1 2,
   opAt 2054 .SUB,
   opAt 2055 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2056 (.Dup ⟨0, by decide⟩),
   opAt 2057 (.Dup ⟨2, by decide⟩),
   opAt 2058 .MUL,
   pushAt 2059 1 2,
   opAt 2060 .SUB,
   opAt 2061 .MUL,
   opAt 2062 (.Dup ⟨0, by decide⟩),
   opAt 2063 (.Dup ⟨2, by decide⟩),
   opAt 2064 .MUL,
   pushAt 2065 1 2,
   opAt 2066 .SUB,
   opAt 2067 .MUL,
   opAt 2068 (.Dup ⟨0, by decide⟩),
   opAt 2069 (.Dup ⟨2, by decide⟩),
   opAt 2070 .MUL,
   pushAt 2071 1 2,
   opAt 2072 .SUB,
   opAt 2073 .MUL,
   pushAt 2074 2 1664,
   opAt 2075 .MSTORE,
   opAt 2076 .POP,
   opAt 2077 .POP,
   opAt 2078 .POP,
   opAt 2079 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2111 .JUMPDEST,
   opAt 2112 (.Dup ⟨0, by decide⟩),
   opAt 2113 .ISZERO,
   pushAt 2114 2 3300,
   opAt 2115 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2116 (.Dup ⟨1, by decide⟩),
   pushAt 2117 2 2112,
   pushAt 2118 2 2080,
   opAt 2119 .MCOPY,
   pushAt 2120 0 0,
   pushAt 2121 2 2784,
   opAt 2122 .MLOAD,
   opAt 2123 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2124 2 2080,
   opAt 2125 .MLOAD,
   pushAt 2126 2 1536,
   opAt 2127 .MLOAD,
   opAt 2128 (.Dup ⟨1, by decide⟩),
   opAt 2129 .DIV,
   opAt 2130 (.Swap ⟨0, by decide⟩),
   pushAt 2131 2 1600,
   opAt 2132 .MLOAD,
   opAt 2133 .MUL,
   pushAt 2134 2 1536,
   opAt 2135 .MLOAD,
   pushAt 2136 2 2112,
   opAt 2137 .MLOAD,
   opAt 2138 .DIV,
   opAt 2139 .ADD,
   pushAt 2140 2 1568,
   opAt 2141 .MLOAD,
   opAt 2142 (.Dup ⟨0, by decide⟩),
   pushAt 2143 2 1632,
   opAt 2144 .MLOAD,
   opAt 2145 (.Dup ⟨4, by decide⟩),
   opAt 2146 .MULMOD,
   opAt 2147 (.Dup ⟨2, by decide⟩),
   opAt 2148 .ADDMOD,
   opAt 2149 (.Swap ⟨0, by decide⟩),
   opAt 2150 .SUB,
   pushAt 2151 2 1664,
   opAt 2152 .MLOAD,
   opAt 2153 .MUL,
   opAt 2154 (.Dup ⟨0, by decide⟩),
   pushAt 2155 0 0,
   opAt 2156 .MLOAD,
   opAt 2157 .MUL,
   pushAt 2158 2 2112,
   opAt 2159 .MLOAD,
   opAt 2160 .SUB,
   pushAt 2161 1 32,
   opAt 2162 .MLOAD,
   pushAt 2163 1 128,
   opAt 2164 .SHR,
   opAt 2165 (.Dup ⟨2, by decide⟩),
   pushAt 2166 1 128,
   opAt 2167 .SHR,
   opAt 2168 .MUL,
   opAt 2169 .GT,
   opAt 2170 (.Swap ⟨0, by decide⟩),
   opAt 2171 .SUB,
   opAt 2172 (.Swap ⟨0, by decide⟩),
   pushAt 2173 2 1568,
   opAt 2174 .MLOAD,
   opAt 2175 .GT,
   opAt 2176 .ISZERO,
   pushAt 2177 0 0,
   opAt 2178 .SUB,
   opAt 2179 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2180 0 0,
   pushAt 2181 1 31,
   opAt 2182 .NOT,
   pushAt 2183 0 0,
   opAt 2184 .NOT,
   pushAt 2185 2 2784,
   opAt 2186 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2190 .JUMPDEST,
   pushAt 2191 2 832,
   opAt 2192 (.Dup ⟨1, by decide⟩),
   opAt 2193 .SUB,
   opAt 2194 .MLOAD,
   opAt 2195 (.Dup ⟨2, by decide⟩),
   opAt 2196 (.Dup ⟨6, by decide⟩),
   opAt 2197 (.Dup ⟨2, by decide⟩),
   opAt 2198 .MUL,
   opAt 2199 (.Swap ⟨1, by decide⟩),
   opAt 2200 (.Dup ⟨7, by decide⟩),
   opAt 2201 .MULMOD,
   opAt 2202 (.Dup ⟨1, by decide⟩),
   opAt 2203 (.Dup ⟨1, by decide⟩),
   opAt 2204 .LT,
   opAt 2205 .SUB,
   opAt 2206 (.Dup ⟨5, by decide⟩),
   opAt 2207 (.Dup ⟨2, by decide⟩),
   opAt 2208 .ADD,
   opAt 2209 (.Dup ⟨0, by decide⟩),
   opAt 2210 (.Swap ⟨6, by decide⟩),
   opAt 2211 .GT,
   opAt 2212 .SUB,
   opAt 2213 .SUB,
   opAt 2214 (.Dup ⟨4, by decide⟩),
   opAt 2215 (.Dup ⟨2, by decide⟩),
   opAt 2216 .MLOAD,
   opAt 2217 .ADD,
   opAt 2218 (.Dup ⟨0, by decide⟩),
   opAt 2219 (.Swap ⟨5, by decide⟩),
   opAt 2220 .GT,
   opAt 2221 .ADD,
   opAt 2222 (.Swap ⟨3, by decide⟩),
   opAt 2223 (.Dup ⟨1, by decide⟩),
   opAt 2224 .MSTORE,
   opAt 2225 (.Dup ⟨2, by decide⟩),
   opAt 2226 .ADD,
   pushAt 2338 2 2080,
   opAt 2339 (.Dup ⟨1, by decide⟩),
   opAt 2340 .GT,
   pushAt 2341 2 2951,
   opAt 2342 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2343 .POP,
   opAt 2344 .POP,
   opAt 2345 .POP,
   pushAt 2346 2 2080,
   opAt 2347 .MLOAD,
   opAt 2348 (.Dup ⟨1, by decide⟩),
   opAt 2349 .ADD,
   opAt 2350 (.Dup ⟨0, by decide⟩),
   opAt 2351 (.Swap ⟨1, by decide⟩),
   opAt 2352 .GT,
   opAt 2353 (.Dup ⟨1, by decide⟩),
   opAt 2354 (.Dup ⟨3, by decide⟩),
   opAt 2355 .GT,
   opAt 2356 .GT,
   opAt 2357 (.Swap ⟨1, by decide⟩),
   opAt 2358 (.Swap ⟨0, by decide⟩),
   opAt 2359 .SUB,
   opAt 2360 (.Dup ⟨0, by decide⟩),
   pushAt 2361 2 2080,
   opAt 2362 .MSTORE,
   opAt 2363 (.Dup ⟨1, by decide⟩),
   opAt 2364 .OR,
   pushAt 2365 2 3156,
   opAt 2366 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2373 .JUMPDEST,
   opAt 2374 .ISZERO,
   pushAt 2375 2 3241,
   opAt 2376 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2377 .JUMPDEST,
   pushAt 2378 0 0,
   pushAt 2379 2 2784,
   opAt 2380 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2381 .JUMPDEST,
   opAt 2382 (.Dup ⟨0, by decide⟩),
   opAt 2383 .MLOAD,
   pushAt 2384 3 2112,
   opAt 2385 (.Dup ⟨2, by decide⟩),
   opAt 2386 .SUB,
   opAt 2387 .MLOAD,
   opAt 2388 (.Dup ⟨1, by decide⟩),
   opAt 2389 .ADD,
   opAt 2390 (.Swap ⟨0, by decide⟩),
   opAt 2391 (.Dup ⟨1, by decide⟩),
   opAt 2392 .LT,
   opAt 2393 (.Swap ⟨0, by decide⟩),
   opAt 2394 (.Dup ⟨3, by decide⟩),
   opAt 2395 .ADD,
   opAt 2396 (.Swap ⟨2, by decide⟩),
   opAt 2397 (.Dup ⟨3, by decide⟩),
   opAt 2398 .LT,
   opAt 2399 .OR,
   opAt 2400 (.Swap ⟨1, by decide⟩),
   opAt 2401 (.Dup ⟨1, by decide⟩),
   opAt 2402 .MSTORE,
   pushAt 2403 1 31,
   opAt 2404 .NOT,
   opAt 2405 .ADD,
   pushAt 2406 2 2111,
   opAt 2407 (.Dup ⟨1, by decide⟩),
   opAt 2408 .GT,
   pushAt 2409 2 3168,
   opAt 2410 .JUMPI,
   opAt 2411 .JUMPDEST,
   opAt 2412 .JUMPDEST,
   opAt 2413 .JUMPDEST,
   opAt 2414 .JUMPDEST,
   opAt 2415 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2416 .POP,
   pushAt 2417 2 2080,
   opAt 2418 .MLOAD,
   opAt 2419 (.Dup ⟨1, by decide⟩),
   opAt 2420 .ADD,
   opAt 2421 (.Dup ⟨0, by decide⟩),
   pushAt 2422 2 2080,
   opAt 2423 .MSTORE,
   opAt 2424 .LT,
   opAt 2425 .ISZERO,
   pushAt 2426 2 3162,
   opAt 2427 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2428 .JUMPDEST,
   pushAt 2429 2 2080,
   opAt 2430 .MLOAD,
   opAt 2431 (.Dup ⟨0, by decide⟩),
   opAt 2432 .ISZERO,
   pushAt 2433 2 3146,
   opAt 2434 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2428 .JUMPDEST,
   pushAt 2429 2 2080,
   opAt 2430 .MLOAD,
   opAt 2431 (.Dup ⟨0, by decide⟩),
   opAt 2432 .ISZERO,
   pushAt 2433 2 3146,
   opAt 2434 .JUMPI,
   opAt 2435 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2436 .JUMPDEST,
   pushAt 2437 0 0,
   pushAt 2438 2 2784,
   opAt 2439 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2440 .JUMPDEST,
   opAt 2441 (.Dup ⟨0, by decide⟩),
   opAt 2442 .MLOAD,
   pushAt 2443 2 2112,
   opAt 2444 (.Dup ⟨2, by decide⟩),
   opAt 2445 .SUB,
   opAt 2446 .MLOAD,
   opAt 2447 (.Dup ⟨1, by decide⟩),
   opAt 2448 (.Dup ⟨1, by decide⟩),
   opAt 2449 .GT,
   opAt 2450 (.Swap ⟨1, by decide⟩),
   opAt 2451 .SUB,
   opAt 2452 (.Dup ⟨3, by decide⟩),
   opAt 2453 (.Dup ⟨1, by decide⟩),
   opAt 2454 .LT,
   opAt 2455 (.Swap ⟨0, by decide⟩),
   opAt 2456 (.Dup ⟨4, by decide⟩),
   opAt 2457 (.Swap ⟨0, by decide⟩),
   opAt 2458 .SUB,
   opAt 2459 (.Dup ⟨3, by decide⟩),
   opAt 2460 .MSTORE,
   opAt 2461 .OR,
   opAt 2462 (.Swap ⟨1, by decide⟩),
   opAt 2463 .POP,
   pushAt 2464 1 31,
   opAt 2465 .NOT,
   opAt 2466 .ADD,
   pushAt 2467 2 2111,
   opAt 2468 (.Dup ⟨1, by decide⟩),
   opAt 2469 .GT,
   pushAt 2470 2 3247,
   opAt 2471 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2472 .POP,
   pushAt 2473 2 2080,
   opAt 2474 .MLOAD,
   opAt 2475 .SUB,
   pushAt 2476 2 2080,
   opAt 2477 .MSTORE,
   pushAt 2478 2 3229,
   opAt 2479 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2367 .JUMPDEST,
   opAt 2368 .NOT,
   opAt 2369 .ADD,
   pushAt 2370 2 2836,
   pushAt 2371 2 4284,
   opAt 2372 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2500 (.Dup ⟨0, by decide⟩),
   pushAt 2501 2 2112,
   pushAt 2502 2 512,
   opAt 2503 .MCOPY,
   opAt 2504 (.Dup ⟨0, by decide⟩),
   pushAt 2505 2 1280,
   pushAt 2506 2 1024,
   opAt 2507 .MCOPY,
   pushAt 2508 2 2443,
   opAt 2509 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2600 = true :=
  Artifact.isValidJumpDest_index 1940 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2634 = true :=
  Artifact.isValidJumpDest_index 1962 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2651 = true :=
  Artifact.isValidJumpDest_index 1970 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2666 = true :=
  Artifact.isValidJumpDest_index 1978 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2836 = true :=
  Artifact.isValidJumpDest_index 2111 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2951 = true :=
  Artifact.isValidJumpDest_index 2190 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3162 = true :=
  Artifact.isValidJumpDest_index 2377 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3168 = true :=
  Artifact.isValidJumpDest_index 2381 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3229 = true :=
  Artifact.isValidJumpDest_index 2428 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3247 = true :=
  Artifact.isValidJumpDest_index 2440 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2373 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3241 = true :=
  Artifact.isValidJumpDest_index 2436 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3146 = true :=
  Artifact.isValidJumpDest_index 2367 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3300 = true :=
  Artifact.isValidJumpDest_index 2480 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
