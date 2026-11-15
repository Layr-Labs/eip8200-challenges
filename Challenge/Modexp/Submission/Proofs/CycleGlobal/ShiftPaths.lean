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
  [opAt 638 (.Dup ⟨0,by decide⟩),
   opAt 639 (.Dup ⟨3,by decide⟩),
   opAt 640 .XOR,
   pushAt 641 1 172,
   opAt 642 .JUMPI]
def blk2874 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 643 (.Dup ⟨0,by decide⟩),
   pushAt 644 1 96,
   pushAt 645 2 2112,
   opAt 646 .CALLDATACOPY]
def blkNegW :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2177 (.Dup ⟨0,by decide⟩),
   pushAt 2178 1 128,
   opAt 2179 .EQ,
   pushAt 2180 2 2745,
   opAt 2181 .JUMPI]
def negS8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2182 1 224,
   opAt 2183 .MLOAD,
   pushAt 2184 0 0,
   opAt 2185 .SUB,
   pushAt 2186 2 1504,
   opAt 2187 .MSTORE]
def negN8a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2188 1 192,
   opAt 2189 .MLOAD,
   opAt 2190 .NOT,
   pushAt 2191 2 1472,
   opAt 2192 .MSTORE]
def negN8b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2193 1 160,
   opAt 2194 .MLOAD,
   opAt 2195 .NOT,
   pushAt 2196 2 1440,
   opAt 2197 .MSTORE]
def negN8c :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2198 1 128,
   opAt 2199 .MLOAD,
   opAt 2200 .NOT,
   pushAt 2201 2 1408,
   opAt 2202 .MSTORE]
def negN8d :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2203 1 96,
   opAt 2204 .MLOAD,
   opAt 2205 .NOT,
   pushAt 2206 2 1376,
   opAt 2207 .MSTORE]
def negS4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2139 1 96,
   opAt 2140 .MLOAD,
   pushAt 2141 0 0,
   opAt 2142 .SUB,
   pushAt 2143 2 1376,
   opAt 2144 .MSTORE]
def negJ4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2138 .JUMPDEST]
def negJ4b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2145 2 2856,
   opAt 2146 .JUMP]
def negJT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2208 .JUMPDEST]
def blkNeg8 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negS8++negN8a++negN8b++negN8c++negN8d
def blkNeg4 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  negJ4++negS4++negJ4b
def blkNegT :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2208 .JUMPDEST,
   pushAt 2209 1 64,
   opAt 2210 .MLOAD,
   opAt 2211 .NOT,
   pushAt 2212 2 1344,
   opAt 2213 .MSTORE,
   pushAt 2214 1 32,
   opAt 2215 .MLOAD,
   opAt 2216 .NOT,
   pushAt 2217 2 1312,
   opAt 2218 .MSTORE,
   pushAt 2219 0 0,
   opAt 2220 .MLOAD,
   opAt 2221 (.Dup ⟨0,by decide⟩),
   opAt 2222 .NOT,
   pushAt 2223 2 1280,
   opAt 2224 .MSTORE]
def blk2919a :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2225 (.Dup ⟨0,by decide⟩),
   pushAt 2226 0 0,
   opAt 2227 .SUB,
   opAt 2228 (.Dup ⟨1,by decide⟩),
   opAt 2229 .AND]
def blk2919b :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2231 (.Dup ⟨0,by decide⟩),
   pushAt 2232 1 1,
   opAt 2233 .ADD,
   pushAt 2234 2 1600,
   opAt 2235 .MSTORE,
   pushAt 2236 1 255,
   opAt 2237 .SUB,
   opAt 2238 (.Dup ⟨0,by decide⟩),
   pushAt 2239 2 1536,
   opAt 2240 .MSTORE,
   opAt 2241 .SHR,
   opAt 2242 (.Dup ⟨0,by decide⟩),
   pushAt 2243 2 1568,
   opAt 2244 .MSTORE,
   opAt 2245 (.Dup ⟨0,by decide⟩),
   opAt 2246 (.Dup ⟨0,by decide⟩),
   pushAt 2247 0 0,
   opAt 2248 .SUB,
   opAt 2249 .MOD,
   pushAt 2250 2 1632,
   opAt 2251 .MSTORE]
def blkNbHead :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2252 2 2752,
   opAt 2253 .MLOAD,
   opAt 2254 .MLOAD,
   opAt 2255 (.Dup ⟨0,by decide⟩),
   opAt 2256 (.Dup ⟨2,by decide⟩),
   opAt 2257 .MUL]
def blkNbSub :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2258 (.Dup ⟨0,by decide⟩),
   pushAt 2259 1 3,
   opAt 2260 .MUL,
   pushAt 2261 1 2,
   opAt 2262 .XOR,
   opAt 2263 (.Dup ⟨0,by decide⟩),
   opAt 2264 (.Dup ⟨2,by decide⟩),
   opAt 2265 .MUL,
   pushAt 2266 1 2,
   opAt 2267 .SUB,
   opAt 2268 .MUL,
   opAt 2269 (.Dup ⟨0,by decide⟩),
   opAt 2270 (.Dup ⟨2,by decide⟩),
   opAt 2271 .MUL,
   pushAt 2272 1 2,
   opAt 2273 .SUB,
   opAt 2274 .MUL,
   opAt 2275 (.Dup ⟨0,by decide⟩),
   opAt 2276 (.Dup ⟨2,by decide⟩),
   opAt 2277 .MUL,
   pushAt 2278 1 2,
   opAt 2279 .SUB,
   opAt 2280 .MUL,
   opAt 2281 (.Dup ⟨0,by decide⟩),
   opAt 2282 (.Dup ⟨2,by decide⟩),
   opAt 2283 .MUL,
   pushAt 2284 1 2,
   opAt 2285 .SUB,
   opAt 2286 .MUL,
   opAt 2287 (.Dup ⟨0,by decide⟩),
   opAt 2288 (.Dup ⟨2,by decide⟩),
   opAt 2289 .MUL,
   pushAt 2290 1 2,
   opAt 2291 .SUB,
   opAt 2292 .MUL,
   opAt 2293 (.Dup ⟨0,by decide⟩),
   opAt 2294 (.Swap ⟨1,by decide⟩),
   opAt 2295 .MUL,
   pushAt 2296 1 2,
   opAt 2297 .SUB,
   opAt 2298 .MUL]
def blkNbTailHead : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2299 (.Dup ⟨0,by decide⟩),
   opAt 2300 (.Swap ⟨1,by decide⟩),
   opAt 2301 .MUL,
   pushAt 2302 2 1664,
   opAt 2303 .MSTORE,
   opAt 2304 .MUL,
   pushAt 2305 0 0,
   opAt 2306 .SUB,
   pushAt 2307 2 2720,
   opAt 2308 .MSTORE,
   pushAt 2309 2 2766,
   opAt 2310 (.Dup ⟨4,by decide⟩),
   pushAt 2311 1 1,
   opAt 2312 .XOR,
   pushAt 2313 2 3015,
   opAt 2314 .JUMPI]
def blkNbTailByte : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2315 2 2656,
   opAt 2316 .MLOAD,
   opAt 2317 .CALLDATALOAD,
   pushAt 2318 0 0,
   opAt 2319 .BYTE,
   pushAt 2320 1 3,
   opAt 2321 .EQ,
   pushAt 2322 2 7893,
   opAt 2323 .MUL,
   opAt 2324 .ADD]
def blkNbTailJoin : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2325 .JUMPDEST,
   pushAt 2326 1 32,
   opAt 2327 .MLOAD,
   pushAt 2328 1 128,
   opAt 2329 .SHR,
   pushAt 2330 2 1536,
   opAt 2331 .MLOAD,
   pushAt 2332 2 1568,
   opAt 2333 .MLOAD,
   pushAt 2334 2 1664,
   opAt 2335 .MLOAD,
   pushAt 2336 2 1632,
   opAt 2337 .MLOAD,
   pushAt 2338 2 1504,
   opAt 2339 .MLOAD,
   pushAt 2340 2 1472,
   opAt 2341 .MLOAD,
   pushAt 2342 2 1440,
   opAt 2343 .MLOAD,
   pushAt 2344 2 1408,
   opAt 2345 .MLOAD,
   pushAt 2346 2 1376,
   opAt 2347 .MLOAD,
   pushAt 2348 2 1344,
   opAt 2349 .MLOAD,
   pushAt 2350 2 1312,
   opAt 2351 .MLOAD,
   opAt 2352 (.Dup ⟨14,by decide⟩)]
def blkNbTail (esize : Nat) : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  blkNbTailHead++(if UInt256.ofNat esize = UInt256.ofNat 1 then blkNbTailByte else [])++blkNbTailJoin
theorem jumpDestNbJoin : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3015 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2325 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)] at h
  exact h
def blkZero8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 7984 .JUMPDEST,
   opAt 7985 (.Dup ⟨15,by decide⟩),
   pushAt 7986 2 2112,
   pushAt 7987 2 2080,
   opAt 7988 .MCOPY,
   pushAt 7989 2 2080,
   opAt 7990 .MLOAD,
   opAt 7991 (.Dup ⟨14,by decide⟩),
   pushAt 7992 2 2112,
   opAt 7993 .MLOAD,
   opAt 7994 (.Dup ⟨14,by decide⟩),
   opAt 7995 (.Dup ⟨0,by decide⟩),
   opAt 7996 (.Dup ⟨14,by decide⟩),
   opAt 7997 (.Dup ⟨5,by decide⟩),
   opAt 7998 .MULMOD,
   opAt 7999 (.Dup ⟨2,by decide⟩),
   opAt 8000 .ADDMOD,
   opAt 8001 (.Dup ⟨0,by decide⟩),
   opAt 8002 (.Swap ⟨1,by decide⟩),
   opAt 8003 .SUB,
   opAt 8004 (.Dup ⟨14,by decide⟩),
   opAt 8005 .MUL,
   opAt 8006 (.Swap ⟨1,by decide⟩),
   opAt 8007 (.Dup ⟨2,by decide⟩),
   pushAt 8008 1 128,
   opAt 8009 .SHR,
   opAt 8010 .MUL,
   opAt 8011 .GT,
   opAt 8012 (.Swap ⟨0,by decide⟩),
   opAt 8013 .SUB,
   pushAt 8014 2 8506,
   opAt 8015 .JUMP]
def blkZero4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 8017 .JUMPDEST,
   opAt 8018 (.Dup ⟨15,by decide⟩),
   pushAt 8019 2 2112,
   pushAt 8020 2 2080,
   opAt 8021 .MCOPY,
   pushAt 8022 2 2080,
   opAt 8023 .MLOAD,
   opAt 8024 (.Dup ⟨14,by decide⟩),
   pushAt 8025 2 2112,
   opAt 8026 .MLOAD,
   opAt 8027 (.Dup ⟨14,by decide⟩),
   opAt 8028 (.Dup ⟨0,by decide⟩),
   opAt 8029 (.Dup ⟨14,by decide⟩),
   opAt 8030 (.Dup ⟨5,by decide⟩),
   opAt 8031 .MULMOD,
   opAt 8032 (.Dup ⟨2,by decide⟩),
   opAt 8033 .ADDMOD,
   opAt 8034 (.Dup ⟨0,by decide⟩),
   opAt 8035 (.Swap ⟨1,by decide⟩),
   opAt 8036 .SUB,
   opAt 8037 (.Dup ⟨14,by decide⟩),
   opAt 8038 .MUL,
   opAt 8039 (.Swap ⟨1,by decide⟩),
   opAt 8040 (.Dup ⟨2,by decide⟩),
   pushAt 8041 1 128,
   opAt 8042 .SHR,
   opAt 8043 .MUL,
   opAt 8044 .GT,
   opAt 8045 (.Swap ⟨0,by decide⟩),
   opAt 8046 .SUB,
   pushAt 8047 2 586,
   opAt 8048 .JUMP]
def blkEstimateSuffix8 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 6399 .JUMPDEST,
   pushAt 6400 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 6401 (.Swap ⟨1,by decide⟩),
   opAt 6402 (.Dup ⟨14,by decide⟩),
   opAt 6403 .GT,
   opAt 6404 (.Dup ⟨2,by decide⟩),
   opAt 6405 .ADD,
   opAt 6406 .OR]
def blkEstimateSuffix4 : List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 432 .JUMPDEST,
   pushAt 433 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 434 (.Swap ⟨1,by decide⟩),
   opAt 435 (.Dup ⟨14,by decide⟩),
   opAt 436 .GT,
   opAt 437 (.Dup ⟨2,by decide⟩),
   opAt 438 .ADD,
   opAt 439 .OR]
def blk3013 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 6354 .JUMPDEST]
def blk3018 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 6355 (.Dup ⟨15,by decide⟩),
   pushAt 6356 2 2112,
   pushAt 6357 2 2080,
   opAt 6358 .MCOPY]
def blk3026 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 6359 2 2080,
   opAt 6360 .MLOAD,
   opAt 6361 (.Dup ⟨0,by decide⟩),
   opAt 6362 (.Dup ⟨14,by decide⟩),
   opAt 6363 .SHR,
   opAt 6364 (.Swap ⟨0,by decide⟩),
   pushAt 6365 2 1600,
   opAt 6366 .MLOAD,
   opAt 6367 .SHL,
   pushAt 6368 2 2112,
   opAt 6369 .MLOAD,
   opAt 6370 (.Dup ⟨15,by decide⟩),
   opAt 6371 .SHR,
   opAt 6372 .ADD,
   opAt 6373 (.Dup ⟨13,by decide⟩),
   opAt 6374 (.Dup ⟨0,by decide⟩),
   opAt 6375 (.Dup ⟨13,by decide⟩),
   opAt 6376 (.Dup ⟨4,by decide⟩),
   opAt 6377 .MULMOD,
   opAt 6378 (.Dup ⟨2,by decide⟩),
   opAt 6379 .ADDMOD,
   opAt 6380 (.Swap ⟨0,by decide⟩),
   opAt 6381 .SUB,
   opAt 6382 (.Dup ⟨12,by decide⟩),
   opAt 6383 .MUL,
   opAt 6384 (.Dup ⟨15,by decide⟩),
   opAt 6385 (.Dup ⟨1,by decide⟩),
   pushAt 6386 1 128,
   opAt 6387 .SHR,
   opAt 6388 .MUL,
   opAt 6389 (.Dup ⟨1,by decide⟩),
   pushAt 6390 0 0,
   opAt 6391 .MLOAD,
   opAt 6392 .MUL,
   pushAt 6393 2 2112,
   opAt 6394 .MLOAD,
   opAt 6395 .SUB,
   opAt 6396 .LT,
   opAt 6397 (.Swap ⟨0,by decide⟩),
   opAt 6398 .SUB,
   opAt 6399 .JUMPDEST,
   pushAt 6400 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 6401 (.Swap ⟨1,by decide⟩),
   opAt 6402 (.Dup ⟨14,by decide⟩),
   opAt 6403 .GT,
   opAt 6404 (.Dup ⟨2,by decide⟩),
   opAt 6405 .ADD,
   opAt 6406 .OR]
def blk3013h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 387 .JUMPDEST]
def blk3018h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 388 (.Dup ⟨15,by decide⟩),
   pushAt 389 2 2112,
   pushAt 390 2 2080,
   opAt 391 .MCOPY]
def blk3026h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 392 2 2080,
   opAt 393 .MLOAD,
   opAt 394 (.Dup ⟨0,by decide⟩),
   opAt 395 (.Dup ⟨14,by decide⟩),
   opAt 396 .SHR,
   opAt 397 (.Swap ⟨0,by decide⟩),
   pushAt 398 2 1600,
   opAt 399 .MLOAD,
   opAt 400 .SHL,
   pushAt 401 2 2112,
   opAt 402 .MLOAD,
   opAt 403 (.Dup ⟨15,by decide⟩),
   opAt 404 .SHR,
   opAt 405 .ADD,
   opAt 406 (.Dup ⟨13,by decide⟩),
   opAt 407 (.Dup ⟨0,by decide⟩),
   opAt 408 (.Dup ⟨13,by decide⟩),
   opAt 409 (.Dup ⟨4,by decide⟩),
   opAt 410 .MULMOD,
   opAt 411 (.Dup ⟨2,by decide⟩),
   opAt 412 .ADDMOD,
   opAt 413 (.Swap ⟨0,by decide⟩),
   opAt 414 .SUB,
   opAt 415 (.Dup ⟨12,by decide⟩),
   opAt 416 .MUL,
   opAt 417 (.Dup ⟨15,by decide⟩),
   opAt 418 (.Dup ⟨1,by decide⟩),
   pushAt 419 1 128,
   opAt 420 .SHR,
   opAt 421 .MUL,
   opAt 422 (.Dup ⟨1,by decide⟩),
   pushAt 423 0 0,
   opAt 424 .MLOAD,
   opAt 425 .MUL,
   pushAt 426 2 2112,
   opAt 427 .MLOAD,
   opAt 428 .SUB,
   opAt 429 .LT,
   opAt 430 (.Swap ⟨0,by decide⟩),
   opAt 431 .SUB,
   opAt 432 .JUMPDEST,
   pushAt 433 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 434 (.Swap ⟨1,by decide⟩),
   opAt 435 (.Dup ⟨14,by decide⟩),
   opAt 436 .GT,
   opAt 437 (.Dup ⟨2,by decide⟩),
   opAt 438 .ADD,
   opAt 439 .OR]
def blk3125Unc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 6621 2 2080,
   opAt 6622 .MLOAD,
   opAt 6623 .ADD,
   opAt 6624 .SUB,
   pushAt 6625 2 3103,
   opAt 6626 .JUMPI,
   opAt 2379 .JUMPDEST,
   pushAt 2380 2 2080,
   opAt 2381 .MSTORE]
def blk3125hUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 542 2 2080,
   opAt 543 .MLOAD,
   opAt 544 .ADD,
   opAt 545 .SUB,
   pushAt 546 2 3103,
   opAt 547 .JUMPI,
   opAt 2379 .JUMPDEST,
   pushAt 2380 2 2080,
   opAt 2381 .MSTORE]
def blk3125 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 6621 2 2080,
   opAt 6622 .MLOAD,
   opAt 6623 .ADD,
   opAt 6624 .SUB,
   pushAt 6625 2 3103,
   opAt 6626 .JUMPI]
def blkUnc :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3153 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2382 .JUMPDEST,
   pushAt 2383 0 0,
   pushAt 2384 2 2784,
   opAt 2385 .MLOAD]
def blk3157 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2386 .JUMPDEST,
   opAt 2387 (.Dup ⟨0,by decide⟩),
   opAt 2388 .MLOAD,
   pushAt 2389 2 2112,
   opAt 2390 (.Dup ⟨2,by decide⟩),
   opAt 2391 .SUB,
   opAt 2392 .MLOAD,
   opAt 2393 (.Dup ⟨1,by decide⟩),
   opAt 2394 .ADD,
   opAt 2395 (.Swap ⟨0,by decide⟩),
   opAt 2396 (.Dup ⟨1,by decide⟩),
   opAt 2397 .LT,
   opAt 2398 (.Swap ⟨0,by decide⟩),
   opAt 2399 (.Dup ⟨3,by decide⟩),
   opAt 2400 .ADD,
   opAt 2401 (.Swap ⟨2,by decide⟩),
   opAt 2402 (.Dup ⟨3,by decide⟩),
   opAt 2403 .LT,
   opAt 2404 .OR,
   opAt 2405 (.Swap ⟨1,by decide⟩),
   opAt 2406 (.Dup ⟨1,by decide⟩),
   opAt 2407 .MSTORE,
   pushAt 2408 1 31,
   opAt 2409 .NOT,
   opAt 2410 .ADD,
   pushAt 2411 2 2111,
   opAt 2412 (.Dup ⟨1,by decide⟩),
   opAt 2413 .GT,
   pushAt 2414 2 3114,
   opAt 2415 .JUMPI]
def blk3192 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 2416 .POP,
   pushAt 2417 2 2080,
   opAt 2418 .MLOAD,
   opAt 2419 (.Dup ⟨1,by decide⟩),
   opAt 2420 .ADD,
   opAt 2421 (.Dup ⟨0,by decide⟩),
   pushAt 2422 2 2080,
   opAt 2423 .MSTORE,
   opAt 2424 .LT,
   opAt 2425 .ISZERO,
   pushAt 2426 2 3108,
   opAt 2427 .JUMPI]
def blk3204 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 2428 2 2080,
   opAt 2429 .MLOAD,
   opAt 2430 (.Dup ⟨0,by decide⟩),
   opAt 2431 .ISZERO,
   opAt 2432 (.Swap ⟨0,by decide⟩),
   opAt 2433 .NOT,
   opAt 2434 (.Swap ⟨0,by decide⟩),
   pushAt 2435 2 10991,
   opAt 2436 .JUMPI]
def blk3253 :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 6627 .ADD,
   opAt 6628 (.Dup ⟨0,by decide⟩),
   opAt 6629 (.Dup ⟨2,by decide⟩),
   opAt 6630 .JUMPI]
def blk3253x :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  []
def blk3125h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [pushAt 542 2 2080,
   opAt 543 .MLOAD,
   opAt 544 .ADD,
   opAt 545 .SUB,
   pushAt 546 2 3103,
   opAt 547 .JUMPI]
def blk3253h :
    List (Challenge.EvmProof.Stepper.Located runtimeArtifact .Osaka) :=
  [opAt 548 .ADD,
   opAt 549 (.Dup ⟨0,by decide⟩),
   opAt 550 (.Dup ⟨2,by decide⟩),
   opAt 551 .JUMPI]
theorem jumpDestBigC : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 172 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 131 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 131 = 172 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4657 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2798 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2172 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2172 = 2798 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNeg4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2745 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2138 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2138 = 2745 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestNegT : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2856 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2208 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2208 = 2856 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest4839 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 8448 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 6354 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 6354 = 8448 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestHead4 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 528 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 387 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 387 = 528 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5115 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3108 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2382 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2382 = 3108 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5121 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3114 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2386 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2386 = 3114 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestLazyStore : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3103 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2379 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2379 = 3103 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDestUnc : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 3103 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2379 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2379 = 3103 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest5311 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 10991 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 8282 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : CycleSubmission.Artifact.artifact.instructionPC 8282 = 10991 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
theorem jumpDest2471 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 2759 = true := by
  have h := CycleSubmission.Global.Binding.jumpDest 2147 (by rw [CycleSubmission.Artifact.instruction_get]; rfl)
  have hp : runtimeArtifact.instructionPC 2147 = 2759 := by
    rw [CycleSubmission.PCCertificate.selectedPC _ (by decide)]; rfl
  simpa only [hp] using h
end CycleSubmission.Global.Fast
namespace CycleSubmission.Global.Fast
open EvmSemantics EvmSemantics.EVM
end CycleSubmission.Global.Fast
