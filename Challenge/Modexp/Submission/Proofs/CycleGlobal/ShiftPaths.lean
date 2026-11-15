import Challenge.Modexp.Submission.Proofs.Prepared.StackArgs
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FastDefs
open CycleSubmission.SharedStackArgs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Fast
private abbrev runtimeArtifact := CycleSubmission.Artifact.artifact
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
def blk2862 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 461 (.Dup ⟨0,by decide⟩),
   opAt 462 (.Dup ⟨3,by decide⟩),
   opAt 463 .XOR,
   pushAt 464 1 172,
   opAt 465 .JUMPI]
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 466 (.Dup ⟨0,by decide⟩),
   pushAt 467 1 96,
   pushAt 468 2 2112,
   opAt 469 .CALLDATACOPY]
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2000 (.Dup ⟨0,by decide⟩),
   pushAt 2001 1 128,
   opAt 2002 .EQ,
   pushAt 2003 2 2499,
   opAt 2004 .JUMPI]
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2005 1 224,
   opAt 2006 .MLOAD,
   pushAt 2007 0 0,
   opAt 2008 .SUB,
   pushAt 2009 2 1504,
   opAt 2010 .MSTORE]
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2011 1 192,
   opAt 2012 .MLOAD,
   opAt 2013 .NOT,
   pushAt 2014 2 1472,
   opAt 2015 .MSTORE]
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2016 1 160,
   opAt 2017 .MLOAD,
   opAt 2018 .NOT,
   pushAt 2019 2 1440,
   opAt 2020 .MSTORE]
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2021 1 128,
   opAt 2022 .MLOAD,
   opAt 2023 .NOT,
   pushAt 2024 2 1408,
   opAt 2025 .MSTORE]
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2026 1 96,
   opAt 2027 .MLOAD,
   opAt 2028 .NOT,
   pushAt 2029 2 1376,
   opAt 2030 .MSTORE]
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1962 1 96,
   opAt 1963 .MLOAD,
   pushAt 1964 0 0,
   opAt 1965 .SUB,
   pushAt 1966 2 1376,
   opAt 1967 .MSTORE]
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1961 .JUMPDEST]
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1968 2 2610,
   opAt 1969 .JUMP]
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2031 .JUMPDEST]
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8++negN8a++negN8b++negN8c++negN8d
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4++negS4++negJ4b
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2031 .JUMPDEST,
   pushAt 2032 1 64,
   opAt 2033 .MLOAD,
   opAt 2034 .NOT,
   pushAt 2035 2 1344,
   opAt 2036 .MSTORE,
   pushAt 2037 1 32,
   opAt 2038 .MLOAD,
   opAt 2039 .NOT,
   pushAt 2040 2 1312,
   opAt 2041 .MSTORE,
   pushAt 2042 0 0,
   opAt 2043 .MLOAD,
   opAt 2044 (.Dup ⟨0,by decide⟩),
   opAt 2045 .NOT,
   pushAt 2046 2 1280,
   opAt 2047 .MSTORE]
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2048 (.Dup ⟨0,by decide⟩),
   pushAt 2049 0 0,
   opAt 2050 .SUB,
   opAt 2051 (.Dup ⟨1,by decide⟩),
   opAt 2052 .AND]
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2054 (.Dup ⟨0,by decide⟩),
   pushAt 2055 1 1,
   opAt 2056 .ADD,
   pushAt 2057 2 1600,
   opAt 2058 .MSTORE,
   pushAt 2059 1 255,
   opAt 2060 .SUB,
   opAt 2061 (.Dup ⟨0,by decide⟩),
   pushAt 2062 2 1536,
   opAt 2063 .MSTORE,
   opAt 2064 .SHR,
   opAt 2065 (.Dup ⟨0,by decide⟩),
   pushAt 2066 2 1568,
   opAt 2067 .MSTORE,
   opAt 2068 (.Dup ⟨0,by decide⟩),
   opAt 2069 (.Dup ⟨0,by decide⟩),
   pushAt 2070 0 0,
   opAt 2071 .SUB,
   opAt 2072 .MOD,
   pushAt 2073 2 1632,
   opAt 2074 .MSTORE]
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2075 2 2752,
   opAt 2076 .MLOAD,
   opAt 2077 .MLOAD,
   opAt 2078 (.Dup ⟨0,by decide⟩),
   opAt 2079 (.Dup ⟨2,by decide⟩),
   opAt 2080 .MUL]
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2081 (.Dup ⟨0,by decide⟩),
   pushAt 2082 1 3,
   opAt 2083 .MUL,
   pushAt 2084 1 2,
   opAt 2085 .XOR,
   opAt 2086 (.Dup ⟨0,by decide⟩),
   opAt 2087 (.Dup ⟨2,by decide⟩),
   opAt 2088 .MUL,
   pushAt 2089 1 2,
   opAt 2090 .SUB,
   opAt 2091 .MUL,
   opAt 2092 (.Dup ⟨0,by decide⟩),
   opAt 2093 (.Dup ⟨2,by decide⟩),
   opAt 2094 .MUL,
   pushAt 2095 1 2,
   opAt 2096 .SUB,
   opAt 2097 .MUL,
   opAt 2098 (.Dup ⟨0,by decide⟩),
   opAt 2099 (.Dup ⟨2,by decide⟩),
   opAt 2100 .MUL,
   pushAt 2101 1 2,
   opAt 2102 .SUB,
   opAt 2103 .MUL,
   opAt 2104 (.Dup ⟨0,by decide⟩),
   opAt 2105 (.Dup ⟨2,by decide⟩),
   opAt 2106 .MUL,
   pushAt 2107 1 2,
   opAt 2108 .SUB,
   opAt 2109 .MUL,
   opAt 2110 (.Dup ⟨0,by decide⟩),
   opAt 2111 (.Dup ⟨2,by decide⟩),
   opAt 2112 .MUL,
   pushAt 2113 1 2,
   opAt 2114 .SUB,
   opAt 2115 .MUL,
   opAt 2116 (.Dup ⟨0,by decide⟩),
   opAt 2117 (.Swap ⟨1,by decide⟩),
   opAt 2118 .MUL,
   pushAt 2119 1 2,
   opAt 2120 .SUB,
   opAt 2121 .MUL]
def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2122 (.Dup ⟨0,by decide⟩),
   opAt 2123 (.Swap ⟨1,by decide⟩),
   opAt 2124 .MUL,
   pushAt 2125 2 1664,
   opAt 2126 .MSTORE,
   opAt 2127 .MUL,
   pushAt 2128 0 0,
   opAt 2129 .SUB,
   pushAt 2130 2 2720,
   opAt 2131 .MSTORE,
   pushAt 2132 2 2520,
   opAt 2133 (.Dup ⟨4,by decide⟩),
   pushAt 2134 1 1,
   opAt 2135 .XOR,
   pushAt 2136 2 2769,
   opAt 2137 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2138 2 2656,
   opAt 2139 .MLOAD,
   opAt 2140 .CALLDATALOAD,
   pushAt 2141 0 0,
   opAt 2142 .BYTE,
   pushAt 2143 1 3,
   opAt 2144 .EQ,
   pushAt 2145 2 8143,
   opAt 2146 .MUL,
   opAt 2147 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2148 .JUMPDEST,
   pushAt 2149 1 32,
   opAt 2150 .MLOAD,
   pushAt 2151 1 128,
   opAt 2152 .SHR,
   pushAt 2153 2 1536,
   opAt 2154 .MLOAD,
   pushAt 2155 2 1568,
   opAt 2156 .MLOAD,
   pushAt 2157 2 1664,
   opAt 2158 .MLOAD,
   pushAt 2159 2 1632,
   opAt 2160 .MLOAD,
   pushAt 2161 2 1504,
   opAt 2162 .MLOAD,
   pushAt 2163 2 1472,
   opAt 2164 .MLOAD,
   pushAt 2165 2 1440,
   opAt 2166 .MLOAD,
   pushAt 2167 2 1408,
   opAt 2168 .MLOAD,
   pushAt 2169 2 1376,
   opAt 2170 .MLOAD,
   pushAt 2171 2 1344,
   opAt 2172 .MLOAD,
   pushAt 2173 2 1312,
   opAt 2174 .MLOAD,
   opAt 2175 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead++(if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else [])++blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2769 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2148 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7987 .JUMPDEST,
   opAt 7988 (.Dup ⟨15,by decide⟩),
   pushAt 7989 2 2112,
   pushAt 7990 2 2080,
   opAt 7991 .MCOPY,
   pushAt 7992 2 2080,
   opAt 7993 .MLOAD,
   opAt 7994 (.Dup ⟨14,by decide⟩),
   pushAt 7995 2 2112,
   opAt 7996 .MLOAD,
   opAt 7997 (.Dup ⟨14,by decide⟩),
   opAt 7998 (.Dup ⟨0,by decide⟩),
   opAt 7999 (.Dup ⟨14,by decide⟩),
   opAt 8000 (.Dup ⟨5,by decide⟩),
   opAt 8001 .MULMOD,
   opAt 8002 (.Dup ⟨2,by decide⟩),
   opAt 8003 .ADDMOD,
   opAt 8004 (.Dup ⟨0,by decide⟩),
   opAt 8005 (.Swap ⟨1,by decide⟩),
   opAt 8006 .SUB,
   opAt 8007 (.Dup ⟨14,by decide⟩),
   opAt 8008 .MUL,
   opAt 8009 (.Swap ⟨1,by decide⟩),
   opAt 8010 (.Dup ⟨2,by decide⟩),
   pushAt 8011 1 128,
   opAt 8012 .SHR,
   opAt 8013 .MUL,
   opAt 8014 .GT,
   opAt 8015 (.Swap ⟨0,by decide⟩),
   opAt 8016 .SUB,
   pushAt 8017 2 3166,
   opAt 8018 .JUMP]
def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8020 .JUMPDEST,
   opAt 8021 (.Dup ⟨15,by decide⟩),
   pushAt 8022 2 2112,
   pushAt 8023 2 2080,
   opAt 8024 .MCOPY,
   pushAt 8025 2 2080,
   opAt 8026 .MLOAD,
   opAt 8027 (.Dup ⟨14,by decide⟩),
   pushAt 8028 2 2112,
   opAt 8029 .MLOAD,
   opAt 8030 (.Dup ⟨14,by decide⟩),
   opAt 8031 (.Dup ⟨0,by decide⟩),
   opAt 8032 (.Dup ⟨14,by decide⟩),
   opAt 8033 (.Dup ⟨5,by decide⟩),
   opAt 8034 .MULMOD,
   opAt 8035 (.Dup ⟨2,by decide⟩),
   opAt 8036 .ADDMOD,
   opAt 8037 (.Dup ⟨0,by decide⟩),
   opAt 8038 (.Swap ⟨1,by decide⟩),
   opAt 8039 .SUB,
   opAt 8040 (.Dup ⟨14,by decide⟩),
   opAt 8041 .MUL,
   opAt 8042 (.Swap ⟨1,by decide⟩),
   opAt 8043 (.Dup ⟨2,by decide⟩),
   pushAt 8044 1 128,
   opAt 8045 .SHR,
   opAt 8046 .MUL,
   opAt 8047 .GT,
   opAt 8048 (.Swap ⟨0,by decide⟩),
   opAt 8049 .SUB,
   pushAt 8050 2 2920,
   opAt 8051 .JUMP]
def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2426 .JUMPDEST,
   pushAt 2427 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2428 (.Swap ⟨1,by decide⟩),
   opAt 2429 (.Dup ⟨14,by decide⟩),
   opAt 2430 .GT,
   opAt 2431 (.Dup ⟨2,by decide⟩),
   opAt 2432 .ADD,
   opAt 2433 .OR]
def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2249 .JUMPDEST,
   pushAt 2250 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2251 (.Swap ⟨1,by decide⟩),
   opAt 2252 (.Dup ⟨14,by decide⟩),
   opAt 2253 .GT,
   opAt 2254 (.Dup ⟨2,by decide⟩),
   opAt 2255 .ADD,
   opAt 2256 .OR]
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2381 .JUMPDEST]
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2382 (.Dup ⟨15,by decide⟩),
   pushAt 2383 2 2112,
   pushAt 2384 2 2080,
   opAt 2385 .MCOPY]
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2386 2 2080,
   opAt 2387 .MLOAD,
   opAt 2388 (.Dup ⟨0,by decide⟩),
   opAt 2389 (.Dup ⟨14,by decide⟩),
   opAt 2390 .SHR,
   opAt 2391 (.Swap ⟨0,by decide⟩),
   pushAt 2392 2 1600,
   opAt 2393 .MLOAD,
   opAt 2394 .SHL,
   pushAt 2395 2 2112,
   opAt 2396 .MLOAD,
   opAt 2397 (.Dup ⟨15,by decide⟩),
   opAt 2398 .SHR,
   opAt 2399 .ADD,
   opAt 2400 (.Dup ⟨13,by decide⟩),
   opAt 2401 (.Dup ⟨0,by decide⟩),
   opAt 2402 (.Dup ⟨13,by decide⟩),
   opAt 2403 (.Dup ⟨4,by decide⟩),
   opAt 2404 .MULMOD,
   opAt 2405 (.Dup ⟨2,by decide⟩),
   opAt 2406 .ADDMOD,
   opAt 2407 (.Swap ⟨0,by decide⟩),
   opAt 2408 .SUB,
   opAt 2409 (.Dup ⟨12,by decide⟩),
   opAt 2410 .MUL,
   opAt 2411 (.Dup ⟨15,by decide⟩),
   opAt 2412 (.Dup ⟨1,by decide⟩),
   pushAt 2413 1 128,
   opAt 2414 .SHR,
   opAt 2415 .MUL,
   opAt 2416 (.Dup ⟨1,by decide⟩),
   pushAt 2417 0 0,
   opAt 2418 .MLOAD,
   opAt 2419 .MUL,
   pushAt 2420 2 2112,
   opAt 2421 .MLOAD,
   opAt 2422 .SUB,
   opAt 2423 .LT,
   opAt 2424 (.Swap ⟨0,by decide⟩),
   opAt 2425 .SUB,
   opAt 2426 .JUMPDEST,
   pushAt 2427 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2428 (.Swap ⟨1,by decide⟩),
   opAt 2429 (.Dup ⟨14,by decide⟩),
   opAt 2430 .GT,
   opAt 2431 (.Dup ⟨2,by decide⟩),
   opAt 2432 .ADD,
   opAt 2433 .OR]
def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2204 .JUMPDEST]
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2205 (.Dup ⟨15,by decide⟩),
   pushAt 2206 2 2112,
   pushAt 2207 2 2080,
   opAt 2208 .MCOPY]
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2209 2 2080,
   opAt 2210 .MLOAD,
   opAt 2211 (.Dup ⟨0,by decide⟩),
   opAt 2212 (.Dup ⟨14,by decide⟩),
   opAt 2213 .SHR,
   opAt 2214 (.Swap ⟨0,by decide⟩),
   pushAt 2215 2 1600,
   opAt 2216 .MLOAD,
   opAt 2217 .SHL,
   pushAt 2218 2 2112,
   opAt 2219 .MLOAD,
   opAt 2220 (.Dup ⟨15,by decide⟩),
   opAt 2221 .SHR,
   opAt 2222 .ADD,
   opAt 2223 (.Dup ⟨13,by decide⟩),
   opAt 2224 (.Dup ⟨0,by decide⟩),
   opAt 2225 (.Dup ⟨13,by decide⟩),
   opAt 2226 (.Dup ⟨4,by decide⟩),
   opAt 2227 .MULMOD,
   opAt 2228 (.Dup ⟨2,by decide⟩),
   opAt 2229 .ADDMOD,
   opAt 2230 (.Swap ⟨0,by decide⟩),
   opAt 2231 .SUB,
   opAt 2232 (.Dup ⟨12,by decide⟩),
   opAt 2233 .MUL,
   opAt 2234 (.Dup ⟨15,by decide⟩),
   opAt 2235 (.Dup ⟨1,by decide⟩),
   pushAt 2236 1 128,
   opAt 2237 .SHR,
   opAt 2238 .MUL,
   opAt 2239 (.Dup ⟨1,by decide⟩),
   pushAt 2240 0 0,
   opAt 2241 .MLOAD,
   opAt 2242 .MUL,
   pushAt 2243 2 2112,
   opAt 2244 .MLOAD,
   opAt 2245 .SUB,
   opAt 2246 .LT,
   opAt 2247 (.Swap ⟨0,by decide⟩),
   opAt 2248 .SUB,
   opAt 2249 .JUMPDEST,
   pushAt 2250 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 2251 (.Swap ⟨1,by decide⟩),
   opAt 2252 (.Dup ⟨14,by decide⟩),
   opAt 2253 .GT,
   opAt 2254 (.Dup ⟨2,by decide⟩),
   opAt 2255 .ADD,
   opAt 2256 .OR]
def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2648 2 2080,
   opAt 2649 .MLOAD,
   opAt 2650 .ADD,
   opAt 2651 .SUB,
   pushAt 2652 2 3469,
   opAt 2653 .JUMPI,
   opAt 2661 .JUMPDEST,
   pushAt 2662 2 2080,
   opAt 2663 .MSTORE]
def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2359 2 2080,
   opAt 2360 .MLOAD,
   opAt 2361 .ADD,
   opAt 2362 .SUB,
   pushAt 2363 2 3469,
   opAt 2364 .JUMPI,
   opAt 2661 .JUMPDEST,
   pushAt 2662 2 2080,
   opAt 2663 .MSTORE]
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2648 2 2080,
   opAt 2649 .MLOAD,
   opAt 2650 .ADD,
   opAt 2651 .SUB,
   pushAt 2652 2 3469,
   opAt 2653 .JUMPI]
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2664 .JUMPDEST,
   pushAt 2665 0 0,
   pushAt 2666 2 2784,
   opAt 2667 .MLOAD]
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2668 .JUMPDEST,
   opAt 2669 (.Dup ⟨0,by decide⟩),
   opAt 2670 .MLOAD,
   pushAt 2671 2 2112,
   opAt 2672 (.Dup ⟨2,by decide⟩),
   opAt 2673 .SUB,
   opAt 2674 .MLOAD,
   opAt 2675 (.Dup ⟨1,by decide⟩),
   opAt 2676 .ADD,
   opAt 2677 (.Swap ⟨0,by decide⟩),
   opAt 2678 (.Dup ⟨1,by decide⟩),
   opAt 2679 .LT,
   opAt 2680 (.Swap ⟨0,by decide⟩),
   opAt 2681 (.Dup ⟨3,by decide⟩),
   opAt 2682 .ADD,
   opAt 2683 (.Swap ⟨2,by decide⟩),
   opAt 2684 (.Dup ⟨3,by decide⟩),
   opAt 2685 .LT,
   opAt 2686 .OR,
   opAt 2687 (.Swap ⟨1,by decide⟩),
   opAt 2688 (.Dup ⟨1,by decide⟩),
   opAt 2689 .MSTORE,
   pushAt 2690 1 31,
   opAt 2691 .NOT,
   opAt 2692 .ADD,
   pushAt 2693 2 2111,
   opAt 2694 (.Dup ⟨1,by decide⟩),
   opAt 2695 .GT,
   pushAt 2696 2 3480,
   opAt 2697 .JUMPI]
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2698 .POP,
   pushAt 2699 2 2080,
   opAt 2700 .MLOAD,
   opAt 2701 (.Dup ⟨1,by decide⟩),
   opAt 2702 .ADD,
   opAt 2703 (.Dup ⟨0,by decide⟩),
   pushAt 2704 2 2080,
   opAt 2705 .MSTORE,
   opAt 2706 .LT,
   opAt 2707 .ISZERO,
   pushAt 2708 2 3474,
   opAt 2709 .JUMPI]
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2710 2 2080,
   opAt 2711 .MLOAD,
   opAt 2712 (.Dup ⟨0,by decide⟩),
   opAt 2713 .ISZERO,
   opAt 2714 (.Swap ⟨0,by decide⟩),
   opAt 2715 .NOT,
   opAt 2716 (.Swap ⟨0,by decide⟩),
   pushAt 2717 2 10995,
   opAt 2718 .JUMPI]
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2654 .ADD,
   opAt 2655 (.Dup ⟨0,by decide⟩),
   opAt 2656 (.Dup ⟨2,by decide⟩),
   opAt 2657 .JUMPI]
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2359 2 2080,
   opAt 2360 .MLOAD,
   opAt 2361 .ADD,
   opAt 2362 .SUB,
   pushAt 2363 2 3469,
   opAt 2364 .JUMPI]
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2365 .ADD,
   opAt 2366 (.Dup ⟨0,by decide⟩),
   opAt 2367 (.Dup ⟨2,by decide⟩),
   opAt 2368 .JUMPI]
theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 172 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 131 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 131 = 172 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2552 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1995 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1995 = 2552 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2499 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1961 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1961 = 2499 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2610 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2031 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2031 = 2610 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3108 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2381 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2381 = 3108 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2862 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2204 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2204 = 2862 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3474 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2664 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2664 = 3474 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3480 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2668 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2668 = 3480 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3469 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2661 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2661 = 3469 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3469 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2661 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2661 = 3469 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10995 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8284 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8284 = 10995 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2513 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1970 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1970 = 2513 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
end CycleSubmission.Global.Fast
namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
