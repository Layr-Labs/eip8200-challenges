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
  [opAt 1978 .JUMPDEST,
   opAt 1979 (.Dup ⟨0, by decide⟩),
   opAt 1980 .MLOAD,
   opAt 1981 .NOT,
   opAt 1982 (.Dup ⟨2, by decide⟩),
   opAt 1983 .ADD,
   opAt 1984 (.Dup ⟨0, by decide⟩),
   opAt 1985 (.Swap ⟨2, by decide⟩),
   opAt 1986 .GT,
   opAt 1987 (.Swap ⟨1, by decide⟩),
   opAt 1988 (.Dup ⟨1, by decide⟩),
   pushAt 1989 2 1280,
   opAt 1990 .ADD,
   opAt 1991 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1992 (.Dup ⟨0, by decide⟩),
   pushAt 1993 1 31,
   opAt 1994 .NOT,
   opAt 1995 .ADD,
   opAt 1996 (.Swap ⟨0, by decide⟩),
   pushAt 1997 2 2666,
   opAt 1998 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
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
   opAt 2226 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2338 2 2080,
   opAt 2339 (.Dup ⟨1, by decide⟩),
   opAt 2340 .GT,
   pushAt 2341 2 2951,
   opAt 2342 .JUMPI]

/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
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
   opAt 2402 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2403 1 31,
   opAt 2404 .NOT,
   opAt 2405 .ADD,
   pushAt 2406 2 2111,
   opAt 2407 (.Dup ⟨1, by decide⟩),
   opAt 2408 .GT,
   pushAt 2409 2 3168,
   opAt 2410 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2411 .JUMPDEST,
   opAt 2412 .JUMPDEST,
   opAt 2413 .JUMPDEST,
   opAt 2414 .JUMPDEST,
   opAt 2415 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
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
   opAt 2461 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2462 (.Swap ⟨1, by decide⟩),
   opAt 2463 .POP,
   pushAt 2464 1 31,
   opAt 2465 .NOT,
   opAt 2466 .ADD,
   pushAt 2467 2 2111,
   opAt 2468 (.Dup ⟨1, by decide⟩),
   opAt 2469 .GT,
   pushAt 2470 2 3247,
   opAt 2471 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
