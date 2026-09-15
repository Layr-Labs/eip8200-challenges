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
  [opAt 1977 .JUMPDEST,
   opAt 1978 (.Dup ⟨0, by decide⟩),
   opAt 1979 .MLOAD,
   opAt 1980 .NOT,
   opAt 1981 (.Dup ⟨2, by decide⟩),
   opAt 1982 .ADD,
   opAt 1983 (.Dup ⟨0, by decide⟩),
   opAt 1984 (.Swap ⟨2, by decide⟩),
   opAt 1985 .GT,
   opAt 1986 (.Swap ⟨1, by decide⟩),
   opAt 1987 (.Dup ⟨1, by decide⟩),
   pushAt 1988 2 1280,
   opAt 1989 .ADD,
   opAt 1990 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1991 (.Dup ⟨0, by decide⟩),
   pushAt 1992 1 32,
   opAt 1993 .SUB,
   opAt 1994 (.Swap ⟨0, by decide⟩),
   opAt 1995 .JUMPDEST,
   pushAt 1996 2 2666,
   opAt 1997 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
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
   opAt 2225 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2337 2 2080,
   opAt 2338 (.Dup ⟨1, by decide⟩),
   opAt 2339 .GT,
   pushAt 2340 2 2951,
   opAt 2341 .JUMPI]

/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
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
   opAt 2401 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2402 1 32,
   opAt 2403 .SUB,
   opAt 2404 .JUMPDEST,
   pushAt 2405 2 2111,
   opAt 2406 (.Dup ⟨1, by decide⟩),
   opAt 2407 .GT,
   pushAt 2408 2 3168,
   opAt 2409 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2410 .JUMPDEST,
   opAt 2411 .JUMPDEST,
   opAt 2412 .JUMPDEST,
   opAt 2413 .JUMPDEST,
   opAt 2414 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
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
   opAt 2460 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2461 (.Swap ⟨1, by decide⟩),
   opAt 2462 .POP,
   pushAt 2463 1 32,
   opAt 2464 .SUB,
   opAt 2465 .JUMPDEST,
   pushAt 2466 2 2111,
   opAt 2467 (.Dup ⟨1, by decide⟩),
   opAt 2468 .GT,
   pushAt 2469 2 3247,
   opAt 2470 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
