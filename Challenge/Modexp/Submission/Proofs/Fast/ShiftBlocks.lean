import Challenge.Modexp.Submission.Proofs.Fast.ShiftPaths
set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Loop-body blocks of the shift-reduce routine split before their exit tests, so
that each block reduction stays small enough for the kernel. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- The negation loop body up to its exit test (`blk2896` instructions 0..14). -/
def blk2896a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1976 .JUMPDEST,
   opAt 1977 (.Dup ⟨0, by decide⟩),
   opAt 1978 .MLOAD,
   opAt 1979 .NOT,
   opAt 1980 (.Dup ⟨2, by decide⟩),
   opAt 1981 .ADD,
   opAt 1982 (.Dup ⟨0, by decide⟩),
   opAt 1983 (.Swap ⟨2, by decide⟩),
   opAt 1984 .GT,
   opAt 1985 (.Swap ⟨1, by decide⟩),
   opAt 1986 (.Dup ⟨1, by decide⟩),
   pushAt 1987 2 1280,
   opAt 1988 .ADD,
   opAt 1989 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1990 (.Dup ⟨0, by decide⟩),
   pushAt 1991 1 31,
   opAt 1992 .NOT,
   opAt 1993 .ADD,
   opAt 1994 (.Swap ⟨0, by decide⟩),
   pushAt 1995 2 2666,
   opAt 1996 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
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
   opAt 2224 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2336 2 2080,
   opAt 2337 (.Dup ⟨1, by decide⟩),
   opAt 2338 .GT,
   pushAt 2339 2 2951,
   opAt 2340 .JUMPI]

/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
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
   opAt 2400 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2401 1 31,
   opAt 2402 .NOT,
   opAt 2403 .ADD,
   pushAt 2404 2 2111,
   opAt 2405 (.Dup ⟨1, by decide⟩),
   opAt 2406 .GT,
   pushAt 2407 2 3168,
   opAt 2408 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2409 .JUMPDEST,
   opAt 2410 .JUMPDEST,
   opAt 2411 .JUMPDEST,
   opAt 2412 .JUMPDEST,
   opAt 2413 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
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
   opAt 2459 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2460 (.Swap ⟨1, by decide⟩),
   opAt 2461 .POP,
   pushAt 2462 1 31,
   opAt 2463 .NOT,
   opAt 2464 .ADD,
   pushAt 2465 2 2111,
   opAt 2466 (.Dup ⟨1, by decide⟩),
   opAt 2467 .GT,
   pushAt 2468 2 3247,
   opAt 2469 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
