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
  [opAt 1942 .JUMPDEST,
   opAt 1943 (.Dup ⟨0, by decide⟩),
   opAt 1944 (.Dup ⟨3, by decide⟩),
   opAt 1945 .EQ,
   pushAt 1946 0 0,
   opAt 1947 .MLOAD,
   pushAt 1948 1 255,
   opAt 1949 .SHR,
   opAt 1950 .AND,
   opAt 1951 .ISZERO,
   pushAt 1952 2 2634,
   opAt 1953 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1954 (.Dup ⟨0, by decide⟩),
   pushAt 1955 1 96,
   pushAt 1956 2 2112,
   opAt 1957 .CALLDATACOPY,
   pushAt 1958 0 0,
   pushAt 1959 2 2080,
   opAt 1960 .MSTORE,
   pushAt 1961 2 2651,
   pushAt 1962 2 4284,
   opAt 1963 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2889 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1964 .JUMPDEST,
   pushAt 1965 1 1,
   pushAt 1966 2 1024,
   opAt 1967 .MSTORE,
   pushAt 1968 2 771,
   pushAt 1969 2 1024,
   pushAt 1970 2 1539,
   opAt 1971 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk2892 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1977 1 1,
   pushAt 1978 2 2752,
   opAt 1979 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk2919 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2001 .POP,
   opAt 2002 .POP,
   pushAt 2003 0 0,
   opAt 2004 .MLOAD,
   opAt 2005 (.Dup ⟨0, by decide⟩),
   pushAt 2006 0 0,
   opAt 2007 .SUB,
   opAt 2008 (.Dup ⟨1, by decide⟩),
   opAt 2009 .AND,
   opAt 2010 (.Dup ⟨0, by decide⟩),
   pushAt 2011 2 1536,
   opAt 2012 .MSTORE,
   opAt 2013 (.Dup ⟨0, by decide⟩),
   opAt 2014 (.Dup ⟨2, by decide⟩),
   opAt 2015 .DIV,
   opAt 2016 (.Dup ⟨0, by decide⟩),
   pushAt 2017 2 1568,
   opAt 2018 .MSTORE,
   opAt 2019 (.Dup ⟨1, by decide⟩),
   opAt 2020 (.Dup ⟨0, by decide⟩),
   pushAt 2021 0 0,
   opAt 2022 .SUB,
   opAt 2023 .DIV,
   pushAt 2024 1 1,
   opAt 2025 .ADD,
   pushAt 2026 2 1600,
   opAt 2027 .MSTORE,
   opAt 2028 (.Dup ⟨0, by decide⟩),
   opAt 2029 (.Dup ⟨0, by decide⟩),
   pushAt 2030 0 0,
   opAt 2031 .SUB,
   opAt 2032 .MOD,
   pushAt 2033 2 1632,
   opAt 2034 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk2956 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2035 (.Dup ⟨0, by decide⟩),
   pushAt 2036 1 3,
   opAt 2037 .MUL,
   pushAt 2038 1 2,
   opAt 2039 .XOR,
   opAt 2040 (.Dup ⟨0, by decide⟩),
   opAt 2041 (.Dup ⟨2, by decide⟩),
   opAt 2042 .MUL,
   pushAt 2043 1 2,
   opAt 2044 .SUB,
   opAt 2045 .MUL,
   opAt 2046 (.Dup ⟨0, by decide⟩),
   opAt 2047 (.Dup ⟨2, by decide⟩),
   opAt 2048 .MUL,
   pushAt 2049 1 2,
   opAt 2050 .SUB,
   opAt 2051 .MUL,
   opAt 2052 (.Dup ⟨0, by decide⟩),
   opAt 2053 (.Dup ⟨2, by decide⟩),
   opAt 2054 .MUL,
   pushAt 2055 1 2,
   opAt 2056 .SUB,
   opAt 2057 .MUL]

/-- Located block of the selected shift-reduce program. -/
def blk2982 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2058 (.Dup ⟨0, by decide⟩),
   opAt 2059 (.Dup ⟨2, by decide⟩),
   opAt 2060 .MUL,
   pushAt 2061 1 2,
   opAt 2062 .SUB,
   opAt 2063 .MUL,
   opAt 2064 (.Dup ⟨0, by decide⟩),
   opAt 2065 (.Dup ⟨2, by decide⟩),
   opAt 2066 .MUL,
   pushAt 2067 1 2,
   opAt 2068 .SUB,
   opAt 2069 .MUL,
   opAt 2070 (.Dup ⟨0, by decide⟩),
   opAt 2071 (.Dup ⟨2, by decide⟩),
   opAt 2072 .MUL,
   pushAt 2073 1 2,
   opAt 2074 .SUB,
   opAt 2075 .MUL,
   pushAt 2076 2 1664,
   opAt 2077 .MSTORE,
   opAt 2078 .POP,
   opAt 2079 .POP,
   opAt 2080 .POP,
   opAt 2081 (.Dup ⟨1, by decide⟩)]

/-- Located block of the selected shift-reduce program. -/
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2113 .JUMPDEST,
   opAt 2114 (.Dup ⟨0, by decide⟩),
   opAt 2115 .ISZERO,
   pushAt 2116 2 3300,
   opAt 2117 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2118 (.Dup ⟨1, by decide⟩),
   pushAt 2119 2 2112,
   pushAt 2120 2 2080,
   opAt 2121 .MCOPY,
   pushAt 2122 0 0,
   pushAt 2123 2 2784,
   opAt 2124 .MLOAD,
   opAt 2125 .MSTORE]

/-- Located block of the selected shift-reduce program. -/
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2126 2 2080,
   opAt 2127 .MLOAD,
   pushAt 2128 2 1536,
   opAt 2129 .MLOAD,
   opAt 2130 (.Dup ⟨1, by decide⟩),
   opAt 2131 .DIV,
   opAt 2132 (.Swap ⟨0, by decide⟩),
   pushAt 2133 2 1600,
   opAt 2134 .MLOAD,
   opAt 2135 .MUL,
   pushAt 2136 2 1536,
   opAt 2137 .MLOAD,
   pushAt 2138 2 2112,
   opAt 2139 .MLOAD,
   opAt 2140 .DIV,
   opAt 2141 .ADD,
   pushAt 2142 2 1568,
   opAt 2143 .MLOAD,
   opAt 2144 (.Dup ⟨0, by decide⟩),
   pushAt 2145 2 1632,
   opAt 2146 .MLOAD,
   opAt 2147 (.Dup ⟨4, by decide⟩),
   opAt 2148 .MULMOD,
   opAt 2149 (.Dup ⟨2, by decide⟩),
   opAt 2150 .ADDMOD,
   opAt 2151 (.Swap ⟨0, by decide⟩),
   opAt 2152 .SUB,
   pushAt 2153 2 1664,
   opAt 2154 .MLOAD,
   opAt 2155 .MUL,
   opAt 2156 (.Dup ⟨0, by decide⟩),
   pushAt 2157 0 0,
   opAt 2158 .MLOAD,
   opAt 2159 .MUL,
   pushAt 2160 2 2112,
   opAt 2161 .MLOAD,
   opAt 2162 .SUB,
   pushAt 2163 1 32,
   opAt 2164 .MLOAD,
   pushAt 2165 1 128,
   opAt 2166 .SHR,
   opAt 2167 (.Dup ⟨2, by decide⟩),
   pushAt 2168 1 128,
   opAt 2169 .SHR,
   opAt 2170 .MUL,
   opAt 2171 .GT,
   opAt 2172 (.Swap ⟨0, by decide⟩),
   opAt 2173 .SUB,
   opAt 2174 (.Swap ⟨0, by decide⟩),
   pushAt 2175 2 1568,
   opAt 2176 .MLOAD,
   opAt 2177 .GT,
   opAt 2178 .ISZERO,
   pushAt 2179 0 0,
   opAt 2180 .SUB,
   opAt 2181 .OR]

/-- Located block of the selected shift-reduce program. -/
def blk3069 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2182 0 0,
   pushAt 2183 1 31,
   opAt 2184 .NOT,
   pushAt 2185 0 0,
   opAt 2186 .NOT,
   pushAt 2187 2 2784,
   opAt 2188 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3077 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2192 .JUMPDEST,
   pushAt 2193 2 832,
   opAt 2194 (.Dup ⟨1, by decide⟩),
   opAt 2195 .SUB,
   opAt 2196 .MLOAD,
   opAt 2197 (.Dup ⟨2, by decide⟩),
   opAt 2198 (.Dup ⟨6, by decide⟩),
   opAt 2199 (.Dup ⟨2, by decide⟩),
   opAt 2200 .MUL,
   opAt 2201 (.Swap ⟨1, by decide⟩),
   opAt 2202 (.Dup ⟨7, by decide⟩),
   opAt 2203 .MULMOD,
   opAt 2204 (.Dup ⟨1, by decide⟩),
   opAt 2205 (.Dup ⟨1, by decide⟩),
   opAt 2206 .LT,
   opAt 2207 .SUB,
   opAt 2208 (.Dup ⟨5, by decide⟩),
   opAt 2209 (.Dup ⟨2, by decide⟩),
   opAt 2210 .ADD,
   opAt 2211 (.Dup ⟨0, by decide⟩),
   opAt 2212 (.Swap ⟨6, by decide⟩),
   opAt 2213 .GT,
   opAt 2214 .SUB,
   opAt 2215 .SUB,
   opAt 2216 (.Dup ⟨4, by decide⟩),
   opAt 2217 (.Dup ⟨2, by decide⟩),
   opAt 2218 .MLOAD,
   opAt 2219 .ADD,
   opAt 2220 (.Dup ⟨0, by decide⟩),
   opAt 2221 (.Swap ⟨5, by decide⟩),
   opAt 2222 .GT,
   opAt 2223 .ADD,
   opAt 2224 (.Swap ⟨3, by decide⟩),
   opAt 2225 (.Dup ⟨1, by decide⟩),
   opAt 2226 .MSTORE,
   opAt 2227 (.Dup ⟨2, by decide⟩),
   opAt 2228 .ADD,
   pushAt 2340 2 2080,
   opAt 2341 (.Dup ⟨1, by decide⟩),
   opAt 2342 .GT,
   pushAt 2343 2 2951,
   opAt 2344 .JUMPI]

/-- The middle block: flags, `TN := Wn - q`, and the three-way exit test on `neg ||| TN`. -/
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2345 .POP,
   opAt 2346 .POP,
   opAt 2347 .POP,
   pushAt 2348 2 2080,
   opAt 2349 .MLOAD,
   opAt 2350 (.Dup ⟨1, by decide⟩),
   opAt 2351 .ADD,
   opAt 2352 (.Dup ⟨0, by decide⟩),
   opAt 2353 (.Swap ⟨1, by decide⟩),
   opAt 2354 .GT,
   opAt 2355 (.Dup ⟨1, by decide⟩),
   opAt 2356 (.Dup ⟨3, by decide⟩),
   opAt 2357 .GT,
   opAt 2358 .GT,
   opAt 2359 (.Swap ⟨1, by decide⟩),
   opAt 2360 (.Swap ⟨0, by decide⟩),
   opAt 2361 .SUB,
   opAt 2362 (.Dup ⟨0, by decide⟩),
   pushAt 2363 2 2080,
   opAt 2364 .MSTORE,
   opAt 2365 (.Dup ⟨1, by decide⟩),
   opAt 2366 .OR,
   pushAt 2367 2 3156,
   opAt 2368 .JUMPI]

/-- `UNC`: `neg ≠ 0` falls into `ADD_LOOP`, `neg = 0` jumps to `SUBL`. -/
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2375 .JUMPDEST,
   opAt 2376 .ISZERO,
   pushAt 2377 2 3241,
   opAt 2378 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2379 .JUMPDEST,
   pushAt 2380 0 0,
   pushAt 2381 2 2784,
   opAt 2382 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2383 .JUMPDEST,
   opAt 2384 (.Dup ⟨0, by decide⟩),
   opAt 2385 .MLOAD,
   opAt 2386 (.Dup ⟨1, by decide⟩),
   pushAt 2387 2 2112,
   opAt 2388 (.Swap ⟨0, by decide⟩),
   opAt 2389 .SUB,
   opAt 2390 .MLOAD,
   opAt 2391 (.Dup ⟨1, by decide⟩),
   opAt 2392 .ADD,
   opAt 2393 (.Dup ⟨0, by decide⟩),
   opAt 2394 (.Dup ⟨2, by decide⟩),
   opAt 2395 .GT,
   opAt 2396 (.Swap ⟨1, by decide⟩),
   opAt 2397 .POP,
   opAt 2398 (.Dup ⟨3, by decide⟩),
   opAt 2399 .ADD,
   opAt 2400 (.Dup ⟨0, by decide⟩),
   opAt 2401 (.Dup ⟨4, by decide⟩),
   opAt 2402 .GT,
   opAt 2403 (.Swap ⟨3, by decide⟩),
   opAt 2404 .POP,
   opAt 2405 (.Dup ⟨2, by decide⟩),
   opAt 2406 .MSTORE,
   opAt 2407 (.Swap ⟨0, by decide⟩),
   opAt 2408 (.Swap ⟨1, by decide⟩),
   opAt 2409 .OR,
   opAt 2410 (.Swap ⟨0, by decide⟩),
   pushAt 2411 1 31,
   opAt 2412 .NOT,
   opAt 2413 .ADD,
   pushAt 2414 2 2111,
   opAt 2415 (.Dup ⟨1, by decide⟩),
   opAt 2416 .GT,
   pushAt 2417 2 3168,
   opAt 2418 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2419 .POP,
   pushAt 2420 2 2080,
   opAt 2421 .MLOAD,
   opAt 2422 (.Dup ⟨1, by decide⟩),
   opAt 2423 .ADD,
   opAt 2424 (.Dup ⟨0, by decide⟩),
   pushAt 2425 2 2080,
   opAt 2426 .MSTORE,
   opAt 2427 .LT,
   opAt 2428 .ISZERO,
   pushAt 2429 2 3162,
   opAt 2430 .JUMPI]

/-- `SUB_CHECK` up to its jump: `TN = 0` jumps to the `CSUB` call with `[TN, k]`. -/
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2431 .JUMPDEST,
   pushAt 2432 2 2080,
   opAt 2433 .MLOAD,
   opAt 2434 (.Dup ⟨0, by decide⟩),
   opAt 2435 .ISZERO,
   pushAt 2436 2 3146,
   opAt 2437 .JUMPI]

/-- `SUB_CHECK` with `TN ≠ 0`: drop the copy and fall into `SUBL`. -/
def blk3204g :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2431 .JUMPDEST,
   pushAt 2432 2 2080,
   opAt 2433 .MLOAD,
   opAt 2434 (.Dup ⟨0, by decide⟩),
   opAt 2435 .ISZERO,
   pushAt 2436 2 3146,
   opAt 2437 .JUMPI,
   opAt 2438 .POP]

/-- `SUBL`: the subtract round's frame `[p, 0]`. -/
def blk3210 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2439 .JUMPDEST,
   pushAt 2440 0 0,
   pushAt 2441 2 2784,
   opAt 2442 .MLOAD]

/-- Located block of the selected shift-reduce program. -/
def blk3213 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2443 .JUMPDEST,
   opAt 2444 (.Dup ⟨0, by decide⟩),
   opAt 2445 .MLOAD,
   pushAt 2446 2 2112,
   opAt 2447 (.Dup ⟨2, by decide⟩),
   opAt 2448 .SUB,
   opAt 2449 .MLOAD,
   opAt 2450 (.Dup ⟨1, by decide⟩),
   opAt 2451 (.Dup ⟨1, by decide⟩),
   opAt 2452 .GT,
   opAt 2453 (.Swap ⟨1, by decide⟩),
   opAt 2454 .SUB,
   opAt 2455 (.Dup ⟨3, by decide⟩),
   opAt 2456 (.Dup ⟨1, by decide⟩),
   opAt 2457 .LT,
   opAt 2458 (.Swap ⟨0, by decide⟩),
   opAt 2459 (.Dup ⟨4, by decide⟩),
   opAt 2460 (.Swap ⟨0, by decide⟩),
   opAt 2461 .SUB,
   opAt 2462 (.Dup ⟨3, by decide⟩),
   opAt 2463 .MSTORE,
   opAt 2464 .OR,
   opAt 2465 (.Swap ⟨1, by decide⟩),
   opAt 2466 .POP,
   pushAt 2467 1 31,
   opAt 2468 .NOT,
   opAt 2469 .ADD,
   pushAt 2470 2 2111,
   opAt 2471 (.Dup ⟨1, by decide⟩),
   opAt 2472 .GT,
   pushAt 2473 2 3247,
   opAt 2474 .JUMPI]

/-- Located block of the selected shift-reduce program. -/
def blk3245 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2475 .POP,
   pushAt 2476 2 2080,
   opAt 2477 .MLOAD,
   opAt 2478 .SUB,
   pushAt 2479 2 2080,
   opAt 2480 .MSTORE,
   pushAt 2481 2 3229,
   opAt 2482 .JUMP]

/-- `k := k - 1` (`NOT ADD` on the zero above `k`), call `CSUB(BASE)` returning to the loop head. -/
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2369 .JUMPDEST,
   opAt 2370 .NOT,
   opAt 2371 .ADD,
   pushAt 2372 2 2836,
   pushAt 2373 2 4284,
   opAt 2374 .JUMP]

/-- Located block of the selected shift-reduce program. -/
def blk3264 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2503 (.Dup ⟨0, by decide⟩),
   pushAt 2504 2 2112,
   pushAt 2505 2 512,
   opAt 2506 .MCOPY,
   opAt 2507 (.Dup ⟨0, by decide⟩),
   pushAt 2508 2 1280,
   pushAt 2509 2 1024,
   opAt 2510 .MCOPY,
   pushAt 2511 2 2443,
   opAt 2512 .JUMP]

theorem jumpDest4608 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2600 = true :=
  Artifact.isValidJumpDest_index 1942 (by rfl)

theorem jumpDest4652 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2634 = true :=
  Artifact.isValidJumpDest_index 1964 (by rfl)

theorem jumpDest4657 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2651 = true :=
  Artifact.isValidJumpDest_index 1972 (by rfl)

theorem jumpDest4664 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2666 = true :=
  Artifact.isValidJumpDest_index 1980 (by rfl)


theorem jumpDest4839 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2836 = true :=
  Artifact.isValidJumpDest_index 2113 (by rfl)

theorem jumpDest4933 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 2951 = true :=
  Artifact.isValidJumpDest_index 2192 (by rfl)

theorem jumpDest5115 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3162 = true :=
  Artifact.isValidJumpDest_index 2379 (by rfl)

theorem jumpDest5121 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3168 = true :=
  Artifact.isValidJumpDest_index 2383 (by rfl)

theorem jumpDest5247 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3229 = true :=
  Artifact.isValidJumpDest_index 2431 (by rfl)

theorem jumpDest5227 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3247 = true :=
  Artifact.isValidJumpDest_index 2443 (by rfl)

theorem jumpDestUnc :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3156 = true :=
  Artifact.isValidJumpDest_index 2375 (by rfl)

theorem jumpDestSubl :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3241 = true :=
  Artifact.isValidJumpDest_index 2439 (by rfl)

theorem jumpDest5311 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3146 = true :=
  Artifact.isValidJumpDest_index 2369 (by rfl)

theorem jumpDest5366 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3300 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
