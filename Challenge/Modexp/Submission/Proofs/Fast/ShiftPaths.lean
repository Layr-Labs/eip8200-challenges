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
  [opAt 1941 .JUMPDEST,
   opAt 1942 (.Dup ⟨0, by decide⟩),
   opAt 1943 (.Dup ⟨3, by decide⟩),
   opAt 1944 .EQ,
   pushAt 1945 0 0,
   opAt 1946 .MLOAD,
   pushAt 1947 1 255,
   opAt 1948 .SHR,
   opAt 1949 .AND,
   opAt 1950 .ISZERO,
   pushAt 1951 2 2634,
   opAt 1952 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1953 (.Dup ⟨0, by decide⟩),
   pushAt 1954 1 96,
   pushAt 1955 2 2112,
   opAt 1956 .CALLDATACOPY,
   pushAt 1957 0 0,
   pushAt 1958 2 2080,
   opAt 1959 .MSTORE,
   pushAt 1960 2 2651,
   pushAt 1961 2 4284,
   opAt 1962 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1963 .JUMPDEST,
   pushAt 1964 1 1,
   pushAt 1965 2 1024,
   opAt 1966 .MSTORE,
   pushAt 1967 2 771,
   pushAt 1968 2 1024,
   pushAt 1969 2 1539,
   opAt 1970 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1976 1 1,
   pushAt 1977 2 2752,
   opAt 1978 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2000 .POP,
   opAt 2001 .POP,
   pushAt 2002 0 0,
   opAt 2003 .MLOAD,
   opAt 2004 (.Dup ⟨0, by decide⟩),
   pushAt 2005 0 0,
   opAt 2006 .SUB,
   opAt 2007 (.Dup ⟨1, by decide⟩),
   opAt 2008 .AND,
   opAt 2009 (.Dup ⟨0, by decide⟩),
   pushAt 2010 2 1536,
   opAt 2011 .MSTORE,
   opAt 2012 (.Dup ⟨0, by decide⟩),
   opAt 2013 (.Dup ⟨2, by decide⟩),
   opAt 2014 .DIV,
   opAt 2015 (.Dup ⟨0, by decide⟩),
   pushAt 2016 2 1568,
   opAt 2017 .MSTORE,
   opAt 2018 (.Dup ⟨1, by decide⟩),
   opAt 2019 (.Dup ⟨0, by decide⟩),
   pushAt 2020 0 0,
   opAt 2021 .SUB,
   opAt 2022 .DIV,
   pushAt 2023 1 1,
   opAt 2024 .ADD,
   pushAt 2025 2 1600,
   opAt 2026 .MSTORE,
   opAt 2027 (.Dup ⟨0, by decide⟩),
   opAt 2028 (.Dup ⟨0, by decide⟩),
   pushAt 2029 0 0,
   opAt 2030 .SUB,
   opAt 2031 .MOD,
   pushAt 2032 2 1632,
   opAt 2033 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2034 (.Dup ⟨0, by decide⟩),
   pushAt 2035 1 3,
   opAt 2036 .MUL,
   pushAt 2037 1 2,
   opAt 2038 .XOR,
   opAt 2039 (.Dup ⟨0, by decide⟩),
   opAt 2040 (.Dup ⟨2, by decide⟩),
   opAt 2041 .MUL,
   pushAt 2042 1 2,
   opAt 2043 .SUB,
   opAt 2044 .MUL,
   opAt 2045 (.Dup ⟨0, by decide⟩),
   opAt 2046 (.Dup ⟨2, by decide⟩),
   opAt 2047 .MUL,
   pushAt 2048 1 2,
   opAt 2049 .SUB,
   opAt 2050 .MUL,
   opAt 2051 (.Dup ⟨0, by decide⟩),
   opAt 2052 (.Dup ⟨2, by decide⟩),
   opAt 2053 .MUL,
   pushAt 2054 1 2,
   opAt 2055 .SUB,
   opAt 2056 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2057 (.Dup ⟨0, by decide⟩),
   opAt 2058 (.Dup ⟨2, by decide⟩),
   opAt 2059 .MUL,
   pushAt 2060 1 2,
   opAt 2061 .SUB,
   opAt 2062 .MUL,
   opAt 2063 (.Dup ⟨0, by decide⟩),
   opAt 2064 (.Dup ⟨2, by decide⟩),
   opAt 2065 .MUL,
   pushAt 2066 1 2,
   opAt 2067 .SUB,
   opAt 2068 .MUL,
   opAt 2069 (.Dup ⟨0, by decide⟩),
   opAt 2070 (.Dup ⟨2, by decide⟩),
   opAt 2071 .MUL,
   pushAt 2072 1 2,
   opAt 2073 .SUB,
   opAt 2074 .MUL,
   pushAt 2075 2 1664,
   opAt 2076 .MSTORE,
   opAt 2077 .POP,
   opAt 2078 .POP,
   opAt 2079 .POP,
   opAt 2080 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2112 .JUMPDEST,
   opAt 2113 (.Dup ⟨0, by decide⟩),
   opAt 2114 .ISZERO,
   pushAt 2115 2 3300,
   opAt 2116 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2117 (.Dup ⟨1, by decide⟩),
   pushAt 2118 2 2112,
   pushAt 2119 2 2080,
   opAt 2120 .MCOPY,
   pushAt 2121 0 0,
   pushAt 2122 2 2784,
   opAt 2123 .MLOAD,
   opAt 2124 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2125 2 2080,
   opAt 2126 .MLOAD,
   pushAt 2127 2 1536,
   opAt 2128 .MLOAD,
   opAt 2129 (.Dup ⟨1, by decide⟩),
   opAt 2130 .DIV,
   opAt 2131 (.Swap ⟨0, by decide⟩),
   pushAt 2132 2 1600,
   opAt 2133 .MLOAD,
   opAt 2134 .MUL,
   pushAt 2135 2 1536,
   opAt 2136 .MLOAD,
   pushAt 2137 2 2112,
   opAt 2138 .MLOAD,
   opAt 2139 .DIV,
   opAt 2140 .ADD,
   pushAt 2141 2 1568,
   opAt 2142 .MLOAD,
   opAt 2143 (.Dup ⟨0, by decide⟩),
   pushAt 2144 2 1632,
   opAt 2145 .MLOAD,
   opAt 2146 (.Dup ⟨4, by decide⟩),
   opAt 2147 .MULMOD,
   opAt 2148 (.Dup ⟨2, by decide⟩),
   opAt 2149 .ADDMOD,
   opAt 2150 (.Swap ⟨0, by decide⟩),
   opAt 2151 .SUB,
   pushAt 2152 2 1664,
   opAt 2153 .MLOAD,
   opAt 2154 .MUL,
   opAt 2155 (.Dup ⟨0, by decide⟩),
   pushAt 2156 0 0,
   opAt 2157 .MLOAD,
   opAt 2158 .MUL,
   pushAt 2159 2 2112,
   opAt 2160 .MLOAD,
   opAt 2161 .SUB,
   pushAt 2162 1 32,
   opAt 2163 .MLOAD,
   pushAt 2164 1 128,
   opAt 2165 .SHR,
   opAt 2166 (.Dup ⟨2, by decide⟩),
   pushAt 2167 1 128,
   opAt 2168 .SHR,
   opAt 2169 .MUL,
   opAt 2170 .GT,
   opAt 2171 (.Swap ⟨0, by decide⟩),
   opAt 2172 .SUB,
   opAt 2173 (.Swap ⟨0, by decide⟩),
   pushAt 2174 2 1568,
   opAt 2175 .MLOAD,
   opAt 2176 .GT,
   opAt 2177 .ISZERO,
   pushAt 2178 0 0,
   opAt 2179 .SUB,
   opAt 2180 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2181 0 0,
   pushAt 2182 1 31,
   opAt 2183 .NOT,
   pushAt 2184 0 0,
   opAt 2185 .NOT,
   pushAt 2186 2 2784,
   opAt 2187 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2191 .JUMPDEST,
   pushAt 2192 2 832,
   opAt 2193 (.Dup ⟨1, by decide⟩),
   opAt 2194 .SUB,
   opAt 2195 .MLOAD,
   opAt 2196 (.Dup ⟨2, by decide⟩),
   opAt 2197 (.Dup ⟨6, by decide⟩),
   opAt 2198 (.Dup ⟨2, by decide⟩),
   opAt 2199 .MUL,
   opAt 2200 (.Swap ⟨1, by decide⟩),
   opAt 2201 (.Dup ⟨7, by decide⟩),
   opAt 2202 .MULMOD,
   opAt 2203 (.Dup ⟨1, by decide⟩),
   opAt 2204 (.Dup ⟨1, by decide⟩),
   opAt 2205 .LT,
   opAt 2206 .SUB,
   opAt 2207 (.Dup ⟨5, by decide⟩),
   opAt 2208 (.Dup ⟨2, by decide⟩),
   opAt 2209 .ADD,
   opAt 2210 (.Dup ⟨0, by decide⟩),
   opAt 2211 (.Swap ⟨6, by decide⟩),
   opAt 2212 .GT,
   opAt 2213 .SUB,
   opAt 2214 .SUB,
   opAt 2215 (.Dup ⟨4, by decide⟩),
   opAt 2216 (.Dup ⟨2, by decide⟩),
   opAt 2217 .MLOAD,
   opAt 2218 .ADD,
   opAt 2219 (.Dup ⟨0, by decide⟩),
   opAt 2220 (.Swap ⟨5, by decide⟩),
   opAt 2221 .GT,
   opAt 2222 .ADD,
   opAt 2223 (.Swap ⟨3, by decide⟩),
   opAt 2224 (.Dup ⟨1, by decide⟩),
   opAt 2225 .MSTORE,
   opAt 2226 (.Dup ⟨2, by decide⟩),
   opAt 2227 .ADD,
   pushAt 2339 2 2080,
   opAt 2340 (.Dup ⟨1, by decide⟩),
   opAt 2341 .GT,
   pushAt 2342 2 2951,
   opAt 2343 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2344 .POP,
   opAt 2345 .POP,
   opAt 2346 .POP,
   pushAt 2347 2 2080,
   opAt 2348 .MLOAD,
   opAt 2349 (.Dup ⟨1, by decide⟩),
   opAt 2350 .ADD,
   opAt 2351 (.Dup ⟨0, by decide⟩),
   opAt 2352 (.Swap ⟨1, by decide⟩),
   opAt 2353 .GT,
   opAt 2354 (.Dup ⟨1, by decide⟩),
   opAt 2355 (.Dup ⟨3, by decide⟩),
   opAt 2356 .GT,
   opAt 2357 .GT,
   opAt 2358 (.Swap ⟨1, by decide⟩),
   opAt 2359 (.Swap ⟨0, by decide⟩),
   opAt 2360 .SUB,
   opAt 2361 (.Dup ⟨0, by decide⟩),
   pushAt 2362 2 2080,
   opAt 2363 .MSTORE,
   opAt 2364 (.Dup ⟨1, by decide⟩),
   opAt 2365 .OR,
   pushAt 2366 2 3156,
   opAt 2367 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2374 .JUMPDEST,
   opAt 2375 .ISZERO,
   pushAt 2376 2 3241,
   opAt 2377 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2378 .JUMPDEST,
   pushAt 2379 0 0,
   pushAt 2380 2 2784,
   opAt 2381 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2382 .JUMPDEST,
   opAt 2383 (.Dup ⟨0, by decide⟩),
   opAt 2384 .MLOAD,
   opAt 2385 (.Dup ⟨1, by decide⟩),
   pushAt 2386 2 2112,
   opAt 2387 (.Swap ⟨0, by decide⟩),
   opAt 2388 .SUB,
   opAt 2389 .MLOAD,
   opAt 2390 (.Dup ⟨1, by decide⟩),
   opAt 2391 .ADD,
   opAt 2392 (.Swap ⟨0, by decide⟩),
   opAt 2393 (.Dup ⟨1, by decide⟩),
   opAt 2394 .LT,
   opAt 2395 (.Swap ⟨0, by decide⟩),
   opAt 2396 (.Dup ⟨3, by decide⟩),
   opAt 2397 .ADD,
   opAt 2398 (.Swap ⟨2, by decide⟩),
   opAt 2399 (.Dup ⟨3, by decide⟩),
   opAt 2400 .LT,
   opAt 2401 .OR,
   opAt 2402 (.Swap ⟨1, by decide⟩),
   opAt 2403 (.Dup ⟨1, by decide⟩),
   opAt 2404 .MSTORE,
   pushAt 2405 1 31,
   opAt 2406 .NOT,
   opAt 2407 .ADD,
   pushAt 2408 2 2111,
   opAt 2409 (.Dup ⟨1, by decide⟩),
   opAt 2410 .GT,
   pushAt 2411 2 3168,
   opAt 2412 .JUMPI,
   opAt 2413 .JUMPDEST,
   opAt 2414 .JUMPDEST,
   opAt 2415 .JUMPDEST,
   opAt 2416 .JUMPDEST,
   opAt 2417 .JUMPDEST]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2418 .POP,
   pushAt 2419 2 2080,
   opAt 2420 .MLOAD,
   opAt 2421 (.Dup ⟨1, by decide⟩),
   opAt 2422 .ADD,
   opAt 2423 (.Dup ⟨0, by decide⟩),
   pushAt 2424 2 2080,
   opAt 2425 .MSTORE,
   opAt 2426 .LT,
   opAt 2427 .ISZERO,
   pushAt 2428 2 3162,
   opAt 2429 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2430 .JUMPDEST,
   pushAt 2431 2 2080,
   opAt 2432 .MLOAD,
   opAt 2433 (.Dup ⟨0, by decide⟩),
   opAt 2434 .ISZERO,
   pushAt 2435 2 3146,
   opAt 2436 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2430 .JUMPDEST,
   pushAt 2431 2 2080,
   opAt 2432 .MLOAD,
   opAt 2433 (.Dup ⟨0, by decide⟩),
   opAt 2434 .ISZERO,
   pushAt 2435 2 3146,
   opAt 2436 .JUMPI,
   opAt 2437 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2438 .JUMPDEST,
   pushAt 2439 0 0,
   pushAt 2440 2 2784,
   opAt 2441 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2442 .JUMPDEST,
   opAt 2443 (.Dup ⟨0, by decide⟩),
   opAt 2444 .MLOAD,
   pushAt 2445 2 2112,
   opAt 2446 (.Dup ⟨2, by decide⟩),
   opAt 2447 .SUB,
   opAt 2448 .MLOAD,
   opAt 2449 (.Dup ⟨1, by decide⟩),
   opAt 2450 (.Dup ⟨1, by decide⟩),
   opAt 2451 .GT,
   opAt 2452 (.Swap ⟨1, by decide⟩),
   opAt 2453 .SUB,
   opAt 2454 (.Dup ⟨3, by decide⟩),
   opAt 2455 (.Dup ⟨1, by decide⟩),
   opAt 2456 .LT,
   opAt 2457 (.Swap ⟨0, by decide⟩),
   opAt 2458 (.Dup ⟨4, by decide⟩),
   opAt 2459 (.Swap ⟨0, by decide⟩),
   opAt 2460 .SUB,
   opAt 2461 (.Dup ⟨3, by decide⟩),
   opAt 2462 .MSTORE,
   opAt 2463 .OR,
   opAt 2464 (.Swap ⟨1, by decide⟩),
   opAt 2465 .POP,
   pushAt 2466 1 31,
   opAt 2467 .NOT,
   opAt 2468 .ADD,
   pushAt 2469 2 2111,
   opAt 2470 (.Dup ⟨1, by decide⟩),
   opAt 2471 .GT,
   pushAt 2472 2 3247,
   opAt 2473 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2474 .POP,
   pushAt 2475 2 2080,
   opAt 2476 .MLOAD,
   opAt 2477 .SUB,
   pushAt 2478 2 2080,
   opAt 2479 .MSTORE,
   pushAt 2480 2 3229,
   opAt 2481 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2368 .JUMPDEST,
   opAt 2369 .NOT,
   opAt 2370 .ADD,
   pushAt 2371 2 2836,
   pushAt 2372 2 4284,
   opAt 2373 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2502 (.Dup ⟨0, by decide⟩),
   pushAt 2503 2 2112,
   pushAt 2504 2 512,
   opAt 2505 .MCOPY,
   opAt 2506 (.Dup ⟨0, by decide⟩),
   pushAt 2507 2 1280,
   pushAt 2508 2 1024,
   opAt 2509 .MCOPY,
   pushAt 2510 2 2443,
   opAt 2511 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2600 = true :=
  Artifact.isValidJumpDest_index 1941 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2634 = true :=
  Artifact.isValidJumpDest_index 1963 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2651 = true :=
  Artifact.isValidJumpDest_index 1971 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2666 = true :=
  Artifact.isValidJumpDest_index 1979 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2836 = true :=
  Artifact.isValidJumpDest_index 2112 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2951 = true :=
  Artifact.isValidJumpDest_index 2191 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3162 = true :=
  Artifact.isValidJumpDest_index 2378 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3168 = true :=
  Artifact.isValidJumpDest_index 2382 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3229 = true :=
  Artifact.isValidJumpDest_index 2430 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3247 = true :=
  Artifact.isValidJumpDest_index 2442 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2374 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3241 = true :=
  Artifact.isValidJumpDest_index 2438 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3146 = true :=
  Artifact.isValidJumpDest_index 2368 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3300 = true :=
  Artifact.isValidJumpDest_index 2482 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
