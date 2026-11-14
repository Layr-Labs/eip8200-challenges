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
  [opAt 465 .JUMPDEST,
   opAt 466 (.Dup dA0),
   opAt 467 (.Dup dA3),
   opAt 468 .XOR,
   pushAt 469 1 207,
   opAt 470 .JUMPI]

 
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 471 (.Dup dA0),
   pushAt 472 1 96,
   pushAt 473 2 2112,
   opAt 474 .CALLDATACOPY,
   pushAt 475 2 2576]


 
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2021 (.Dup dA0),
   pushAt 2022 1 128,
   opAt 2023 .EQ,
   pushAt 2024 2 2522,
   opAt 2025 .JUMPI]

 
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2026 1 224,
   opAt 2027 .MLOAD,
   pushAt 2028 0 0,
   opAt 2029 .SUB,
   pushAt 2030 2 1504,
   opAt 2031 .MSTORE]

 
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2032 1 192,
   opAt 2033 .MLOAD,
   opAt 2034 .NOT,
   pushAt 2035 2 1472,
   opAt 2036 .MSTORE]

 
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2037 1 160,
   opAt 2038 .MLOAD,
   opAt 2039 .NOT,
   pushAt 2040 2 1440,
   opAt 2041 .MSTORE]

 
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2042 1 128,
   opAt 2043 .MLOAD,
   opAt 2044 .NOT,
   pushAt 2045 2 1408,
   opAt 2046 .MSTORE]

 
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2047 1 96,
   opAt 2048 .MLOAD,
   opAt 2049 .NOT,
   pushAt 2050 2 1376,
   opAt 2051 .MSTORE]

 


 


 


 
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1983 1 96,
   opAt 1984 .MLOAD,
   pushAt 1985 0 0,
   opAt 1986 .SUB,
   pushAt 1987 2 1376,
   opAt 1988 .MSTORE]

 
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 1982 .JUMPDEST]

 
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 1989 2 2634,
   opAt 1990 .JUMP]

 
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2052 .JUMPDEST]

 
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8 ++ negN8a ++ negN8b ++ negN8c ++ negN8d

 
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4 ++ negS4 ++ negJ4b

 
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2052 .JUMPDEST,
   pushAt 2053 1 64,
   opAt 2054 .MLOAD,
   opAt 2055 .NOT,
   pushAt 2056 2 1344,
   opAt 2057 .MSTORE,
   pushAt 2058 1 32,
   opAt 2059 .MLOAD,
   opAt 2060 .NOT,
   pushAt 2061 2 1312,
   opAt 2062 .MSTORE,
   pushAt 2063 0 0,
   opAt 2064 .MLOAD,
   opAt 2065 (.Dup dA0),
   opAt 2066 .NOT,
   pushAt 2067 2 1280,
   opAt 2068 .MSTORE]


 
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2069 (.Dup dA0),
   pushAt 2070 0 0,
   opAt 2071 .SUB,
   opAt 2072 (.Dup dA1),
   opAt 2073 .AND]


 

def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2075 (.Dup dA0),
   pushAt 2076 1 1,
   opAt 2077 .ADD,
   pushAt 2078 2 1600,
   opAt 2079 .MSTORE,
   pushAt 2080 1 255,
   opAt 2081 .SUB,
   opAt 2082 (.Dup dA0),
   pushAt 2083 2 1536,
   opAt 2084 .MSTORE,
   opAt 2085 .SHR,
   opAt 2086 (.Dup dA0),
   pushAt 2087 2 1568,
   opAt 2088 .MSTORE,
   opAt 2089 (.Dup dA0),
   opAt 2090 (.Dup dA0),
   pushAt 2091 0 0,
   opAt 2092 .SUB,
   opAt 2093 .MOD,
   pushAt 2094 2 1632,
   opAt 2095 .MSTORE]

 
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2096 2 2752,
   opAt 2097 .MLOAD,
   opAt 2098 .MLOAD,
   opAt 2099 (.Dup dA0),
   opAt 2100 (.Dup dA2),
   opAt 2101 .MUL]

 
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2102 (.Dup dA0),
   pushAt 2103 1 3,
   opAt 2104 .MUL,
   pushAt 2105 1 2,
   opAt 2106 .XOR,
   opAt 2107 (.Dup dA0),
   opAt 2108 (.Dup dA2),
   opAt 2109 .MUL,
   pushAt 2110 1 2,
   opAt 2111 .SUB,
   opAt 2112 .MUL,
   opAt 2113 (.Dup dA0),
   opAt 2114 (.Dup dA2),
   opAt 2115 .MUL,
   pushAt 2116 1 2,
   opAt 2117 .SUB,
   opAt 2118 .MUL,
   opAt 2119 (.Dup dA0),
   opAt 2120 (.Dup dA2),
   opAt 2121 .MUL,
   pushAt 2122 1 2,
   opAt 2123 .SUB,
   opAt 2124 .MUL,
   opAt 2125 (.Dup dA0),
   opAt 2126 (.Dup dA2),
   opAt 2127 .MUL,
   pushAt 2128 1 2,
   opAt 2129 .SUB,
   opAt 2130 .MUL,
   opAt 2131 (.Dup dA0),
   opAt 2132 (.Dup dA2),
   opAt 2133 .MUL,
   pushAt 2134 1 2,
   opAt 2135 .SUB,
   opAt 2136 .MUL,
   opAt 2137 (.Dup dA0),
   opAt 2138 (.Swap sA1),
   opAt 2139 .MUL,
   pushAt 2140 1 2,
   opAt 2141 .SUB,
   opAt 2142 .MUL]

 

def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2143 (.Dup dA0),
   opAt 2144 (.Swap sA1),
   opAt 2145 .MUL,
   pushAt 2146 2 1664,
   opAt 2147 .MSTORE,
   opAt 2148 .MUL,
   pushAt 2149 0 0,
   opAt 2150 .SUB,
   pushAt 2151 2 2720,
   opAt 2152 .MSTORE,
   pushAt 2153 2 2544,
   opAt 2154 (.Dup dA4),
   pushAt 2155 1 1,
   opAt 2156 .XOR,
   pushAt 2157 2 2793,
   opAt 2158 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2159 2 2656,
   opAt 2160 .MLOAD,
   opAt 2161 .CALLDATALOAD,
   pushAt 2162 0 0,
   opAt 2163 .BYTE,
   pushAt 2164 1 3,
   opAt 2165 .EQ,
   pushAt 2166 2 7211,
   opAt 2167 .MUL,
   opAt 2168 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2169 .JUMPDEST,
   pushAt 2170 1 32,
   opAt 2171 .MLOAD,
   pushAt 2172 1 128,
   opAt 2173 .SHR,
   pushAt 2174 2 1536,
   opAt 2175 .MLOAD,
   pushAt 2176 2 1568,
   opAt 2177 .MLOAD,
   pushAt 2178 2 1664,
   opAt 2179 .MLOAD,
   pushAt 2180 2 1632,
   opAt 2181 .MLOAD,
   pushAt 2182 2 1504,
   opAt 2183 .MLOAD,
   pushAt 2184 2 1472,
   opAt 2185 .MLOAD,
   pushAt 2186 2 1440,
   opAt 2187 .MLOAD,
   pushAt 2188 2 1408,
   opAt 2189 .MLOAD,
   pushAt 2190 2 1376,
   opAt 2191 .MLOAD,
   pushAt 2192 2 1344,
   opAt 2193 .MLOAD,
   pushAt 2194 2 1312,
   opAt 2195 .MLOAD,
   opAt 2196 (.Dup dA14)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead ++ (if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else []) ++ blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2793 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2169 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h

 

def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7428 .JUMPDEST,
   opAt 7429 (.Dup dA15),
   pushAt 7430 2 2112,
   pushAt 7431 2 2080,
   opAt 7432 .MCOPY,
   pushAt 7433 2 2080,
   opAt 7434 .MLOAD,
   opAt 7435 (.Dup dA14),
   pushAt 7436 2 2112,
   opAt 7437 .MLOAD,
   opAt 7438 (.Dup dA14),
   opAt 7439 (.Dup dA0),
   opAt 7440 (.Dup dA14),
   opAt 7441 (.Dup dA5),
   opAt 7442 .MULMOD,
   opAt 7443 (.Dup dA2),
   opAt 7444 .ADDMOD,
   opAt 7445 (.Dup dA0),
   opAt 7446 (.Swap sA1),
   opAt 7447 .SUB,
   opAt 7448 (.Dup dA14),
   opAt 7449 .MUL,
   opAt 7450 (.Swap sA1),
   opAt 7451 (.Dup dA2),
   pushAt 7452 1 128,
   opAt 7453 .SHR,
   opAt 7454 .MUL,
   opAt 7455 .GT,
   opAt 7456 (.Swap sA0),
   opAt 7457 .SUB,
   pushAt 7458 2 2942,
   opAt 7459 .JUMP]

def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7574 .JUMPDEST,
   opAt 7575 (.Dup dA15),
   pushAt 7576 2 2112,
   pushAt 7577 2 2080,
   opAt 7578 .MCOPY,
   pushAt 7579 2 2080,
   opAt 7580 .MLOAD,
   opAt 7581 (.Dup dA14),
   pushAt 7582 2 2112,
   opAt 7583 .MLOAD,
   opAt 7584 (.Dup dA14),
   opAt 7585 (.Dup dA0),
   opAt 7586 (.Dup dA14),
   opAt 7587 (.Dup dA5),
   opAt 7588 .MULMOD,
   opAt 7589 (.Dup dA2),
   opAt 7590 .ADDMOD,
   opAt 7591 (.Dup dA0),
   opAt 7592 (.Swap sA1),
   opAt 7593 .SUB,
   opAt 7594 (.Dup dA14),
   opAt 7595 .MUL,
   opAt 7596 (.Swap sA1),
   opAt 7597 (.Dup dA2),
   pushAt 7598 1 128,
   opAt 7599 .SHR,
   opAt 7600 .MUL,
   opAt 7601 .GT,
   opAt 7602 (.Swap sA0),
   opAt 7603 .SUB,
   pushAt 7604 2 10566,
   opAt 7605 .JUMP]

def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2270 .JUMPDEST,
   pushAt 2271 0 0,
   opAt 2272 .NOT,
   opAt 2273 (.Swap sA1),
   opAt 2274 (.Dup dA14),
   opAt 2275 .GT,
   opAt 2276 (.Dup dA2),
   opAt 2277 .ADD,
   opAt 2278 .OR]

def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8258 .JUMPDEST,
   pushAt 8259 0 0,
   opAt 8260 .NOT,
   opAt 8261 (.Swap sA1),
   opAt 8262 (.Dup dA14),
   opAt 8263 .GT,
   opAt 8264 (.Dup dA2),
   opAt 8265 .ADD,
   opAt 8266 .OR]

def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2225 .JUMPDEST]

 
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2226 (.Dup dA15),
   pushAt 2227 2 2112,
   pushAt 2228 2 2080,
   opAt 2229 .MCOPY]

 
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2230 2 2080,
   opAt 2231 .MLOAD,
   opAt 2232 (.Dup dA0),
   opAt 2233 (.Dup dA14),
   opAt 2234 .SHR,
   opAt 2235 (.Swap sA0),
   pushAt 2236 2 1600,
   opAt 2237 .MLOAD,
   opAt 2238 .SHL,
   pushAt 2239 2 2112,
   opAt 2240 .MLOAD,
   opAt 2241 (.Dup dA15),
   opAt 2242 .SHR,
   opAt 2243 .ADD,
   opAt 2244 (.Dup dA13),
   opAt 2245 (.Dup dA0),
   opAt 2246 (.Dup dA13),
   opAt 2247 (.Dup dA4),
   opAt 2248 .MULMOD,
   opAt 2249 (.Dup dA2),
   opAt 2250 .ADDMOD,
   opAt 2251 (.Swap sA0),
   opAt 2252 .SUB,
   opAt 2253 (.Dup dA12),
   opAt 2254 .MUL,
   opAt 2255 (.Dup dA15),
   opAt 2256 (.Dup dA1),
   pushAt 2257 1 128,
   opAt 2258 .SHR,
   opAt 2259 .MUL,
   opAt 2260 (.Dup dA1),
   pushAt 2261 0 0,
   opAt 2262 .MLOAD,
   opAt 2263 .MUL,
   pushAt 2264 2 2112,
   opAt 2265 .MLOAD,
   opAt 2266 .SUB,
   opAt 2267 .LT,
   opAt 2268 (.Swap sA0),
   opAt 2269 .SUB,
   opAt 2270 .JUMPDEST,
   pushAt 2271 0 0,
   opAt 2272 .NOT,
   opAt 2273 (.Swap sA1),
   opAt 2274 (.Dup dA14),
   opAt 2275 .GT,
   opAt 2276 (.Dup dA2),
   opAt 2277 .ADD,
   opAt 2278 .OR]



def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8213 .JUMPDEST]

 
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8214 (.Dup dA15),
   pushAt 8215 2 2112,
   pushAt 8216 2 2080,
   opAt 8217 .MCOPY]

 
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
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
   opAt 8258 .JUMPDEST,
   pushAt 8259 0 0,
   opAt 8260 .NOT,
   opAt 8261 (.Swap sA1),
   opAt 8262 (.Dup dA14),
   opAt 8263 .GT,
   opAt 8264 (.Dup dA2),
   opAt 8265 .ADD,
   opAt 8266 .OR]



 




def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2493 2 2080,
   opAt 2494 .MLOAD,
   opAt 2495 .ADD,
   opAt 2496 .SUB,
   opAt 2497 (.Dup dA0),
   pushAt 2498 2 3219,
   opAt 2499 .JUMPI,
   opAt 2511 .JUMPDEST,
   pushAt 2512 2 2080,
   opAt 2513 .MSTORE]

def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8369 2 2080,
   opAt 8370 .MLOAD,
   opAt 8371 .ADD,
   opAt 8372 .SUB,
   opAt 8373 (.Dup dA0),
   pushAt 8374 2 3219,
   opAt 8375 .JUMPI,
   opAt 2511 .JUMPDEST,
   pushAt 2512 2 2080,
   opAt 2513 .MSTORE]

def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2493 2 2080,
   opAt 2494 .MLOAD,
   opAt 2495 .ADD,
   opAt 2496 .SUB,
   opAt 2497 (.Dup dA0),
   pushAt 2498 2 3219,
   opAt 2499 .JUMPI,
   opAt 2500 (.Swap sA0),
   opAt 2501 .POP]

 
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2514 .POP]

 
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2515 .JUMPDEST,
   pushAt 2516 0 0,
   pushAt 2517 2 2784,
   opAt 2518 .MLOAD]

 
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2519 .JUMPDEST,
   opAt 2520 (.Dup dA0),
   opAt 2521 .MLOAD,
   pushAt 2522 2 2112,
   opAt 2523 (.Dup dA2),
   opAt 2524 .SUB,
   opAt 2525 .MLOAD,
   opAt 2526 (.Dup dA1),
   opAt 2527 .ADD,
   opAt 2528 (.Swap sA0),
   opAt 2529 (.Dup dA1),
   opAt 2530 .LT,
   opAt 2531 (.Swap sA0),
   opAt 2532 (.Dup dA3),
   opAt 2533 .ADD,
   opAt 2534 (.Swap sA2),
   opAt 2535 (.Dup dA3),
   opAt 2536 .LT,
   opAt 2537 .OR,
   opAt 2538 (.Swap sA1),
   opAt 2539 (.Dup dA1),
   opAt 2540 .MSTORE,
   pushAt 2541 1 31,
   opAt 2542 .NOT,
   opAt 2543 .ADD,
   pushAt 2544 2 2111,
   opAt 2545 (.Dup dA1),
   opAt 2546 .GT,
   pushAt 2547 2 3231,
   opAt 2548 .JUMPI]

 
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2549 .POP,
   pushAt 2550 2 2080,
   opAt 2551 .MLOAD,
   opAt 2552 (.Dup dA1),
   opAt 2553 .ADD,
   opAt 2554 (.Dup dA0),
   pushAt 2555 2 2080,
   opAt 2556 .MSTORE,
   opAt 2557 .LT,
   opAt 2558 .ISZERO,
   pushAt 2559 2 3225,
   opAt 2560 .JUMPI]

 
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2561 2 2080,
   opAt 2562 .MLOAD,
   opAt 2563 (.Dup dA0),
   opAt 2564 .ISZERO,
   pushAt 2565 2 3210,
   opAt 2566 .JUMPI]

 
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2502 .JUMPDEST,
   opAt 2503 .NOT,
   opAt 2504 .ADD,
   opAt 2505 (.Dup dA0),
   opAt 2506 (.Dup dA2),
   opAt 2507 .JUMPI]


 

def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []

 
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 8369 2 2080,
   opAt 8370 .MLOAD,
   opAt 8371 .ADD,
   opAt 8372 .SUB,
   opAt 8373 (.Dup dA0),
   pushAt 8374 2 3219,
   opAt 8375 .JUMPI,
   opAt 8376 (.Swap sA0),
   opAt 8377 .POP]

 
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8378 .NOT,
   opAt 8379 .ADD,
   opAt 8380 (.Dup dA0),
   opAt 8381 (.Dup dA2),
   opAt 8382 .JUMPI]


theorem jumpDest4608 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 660 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 465 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 465 = 660 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 207 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 134 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 134 = 207 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2576 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2016 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2016 = 2576 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2522 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1982 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1982 = 2522 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2634 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2052 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2052 = 2634 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2884 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2225 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2225 = 2884 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10508 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8213 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 8213 = 10508 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3225 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2515 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2515 = 3225 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3231 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2519 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2519 = 3231 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3219 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2511 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2511 = 3219 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3219 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2511 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2511 = 3219 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h


theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3210 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2502 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2502 = 3210 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h




theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2536 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 1991 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 1991 = 2536 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h



end CycleSubmission.Global.Fast

namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
