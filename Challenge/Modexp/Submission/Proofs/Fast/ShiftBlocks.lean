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
  [opAt 1979 .JUMPDEST,
   opAt 1980 (.Dup ⟨0, by decide⟩),
   opAt 1981 .MLOAD,
   opAt 1982 .NOT,
   opAt 1983 (.Dup ⟨2, by decide⟩),
   opAt 1984 .ADD,
   opAt 1985 (.Dup ⟨0, by decide⟩),
   opAt 1986 (.Swap ⟨2, by decide⟩),
   opAt 1987 .GT,
   opAt 1988 (.Swap ⟨1, by decide⟩),
   opAt 1989 (.Dup ⟨1, by decide⟩),
   pushAt 1990 2 1280,
   opAt 1991 .ADD,
   opAt 1992 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1993 (.Dup ⟨0, by decide⟩),
   pushAt 1994 1 31,
   opAt 1995 .NOT,
   opAt 1996 .ADD,
   opAt 1997 (.Swap ⟨0, by decide⟩),
   pushAt 1998 2 2666,
   opAt 1999 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
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
   opAt 2227 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2339 2 2080,
   opAt 2340 (.Dup ⟨1, by decide⟩),
   opAt 2341 .GT,
   pushAt 2342 2 2951,
   opAt 2343 .JUMPI]

/-- The add-round body up to its store (`blk3157` instructions 0..22). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2382 .JUMPDEST,
   opAt 2383 (.Dup ⟨0, by decide⟩),
   opAt 2384 .MLOAD,
   pushAt 2385 3 2112,
   opAt 2386 (.Dup ⟨2, by decide⟩),
   opAt 2387 .SUB,
   opAt 2388 .MLOAD,
   opAt 2389 (.Dup ⟨1, by decide⟩),
   opAt 2390 .ADD,
   opAt 2391 (.Swap ⟨0, by decide⟩),
   opAt 2392 (.Dup ⟨1, by decide⟩),
   opAt 2393 .LT,
   opAt 2394 (.Swap ⟨0, by decide⟩),
   opAt 2395 (.Dup ⟨3, by decide⟩),
   opAt 2396 .ADD,
   opAt 2397 (.Swap ⟨2, by decide⟩),
   opAt 2398 (.Dup ⟨3, by decide⟩),
   opAt 2399 .LT,
   opAt 2400 .OR,
   opAt 2401 (.Swap ⟨1, by decide⟩),
   opAt 2402 (.Dup ⟨1, by decide⟩),
   opAt 2403 .MSTORE]

/-- The exit test of the add-round body (`blk3157` instructions 23..30). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2404 1 31,
   opAt 2405 .NOT,
   opAt 2406 .ADD,
   pushAt 2407 2 2111,
   opAt 2408 (.Dup ⟨1, by decide⟩),
   opAt 2409 .GT,
   pushAt 2410 2 3168,
   opAt 2411 .JUMPI]

/-- The five padding `JUMPDEST`s on the add-round fall-through (indices 2413 to 2417). -/
def blk3157c :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2412 .JUMPDEST,
   opAt 2413 .JUMPDEST,
   opAt 2414 .JUMPDEST,
   opAt 2415 .JUMPDEST,
   opAt 2416 .JUMPDEST]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2441 .JUMPDEST,
   opAt 2442 (.Dup ⟨0, by decide⟩),
   opAt 2443 .MLOAD,
   pushAt 2444 2 2112,
   opAt 2445 (.Dup ⟨2, by decide⟩),
   opAt 2446 .SUB,
   opAt 2447 .MLOAD,
   opAt 2448 (.Dup ⟨1, by decide⟩),
   opAt 2449 (.Dup ⟨1, by decide⟩),
   opAt 2450 .GT,
   opAt 2451 (.Swap ⟨1, by decide⟩),
   opAt 2452 .SUB,
   opAt 2453 (.Dup ⟨3, by decide⟩),
   opAt 2454 (.Dup ⟨1, by decide⟩),
   opAt 2455 .LT,
   opAt 2456 (.Swap ⟨0, by decide⟩),
   opAt 2457 (.Dup ⟨4, by decide⟩),
   opAt 2458 (.Swap ⟨0, by decide⟩),
   opAt 2459 .SUB,
   opAt 2460 (.Dup ⟨3, by decide⟩),
   opAt 2461 .MSTORE,
   opAt 2462 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2463 (.Swap ⟨1, by decide⟩),
   opAt 2464 .POP,
   pushAt 2465 1 31,
   opAt 2466 .NOT,
   opAt 2467 .ADD,
   pushAt 2468 2 2111,
   opAt 2469 (.Dup ⟨1, by decide⟩),
   opAt 2470 .GT,
   pushAt 2471 2 3247,
   opAt 2472 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
