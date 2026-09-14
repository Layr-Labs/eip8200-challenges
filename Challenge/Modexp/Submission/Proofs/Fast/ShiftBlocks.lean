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
  [opAt 1980 .JUMPDEST,
   opAt 1981 (.Dup ⟨0, by decide⟩),
   opAt 1982 .MLOAD,
   opAt 1983 .NOT,
   opAt 1984 (.Dup ⟨2, by decide⟩),
   opAt 1985 .ADD,
   opAt 1986 (.Dup ⟨0, by decide⟩),
   opAt 1987 (.Swap ⟨2, by decide⟩),
   opAt 1988 .GT,
   opAt 1989 (.Swap ⟨1, by decide⟩),
   opAt 1990 (.Dup ⟨1, by decide⟩),
   pushAt 1991 2 1280,
   opAt 1992 .ADD,
   opAt 1993 .MSTORE]

/-- The rotated exit test of the negation loop body: `p - 32` stays on the stack, the
jump back to the loop head is taken on the old pointer `p`, and `p = 0` falls into `NEG_DONE`. -/
def blk2896b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1994 (.Dup ⟨0, by decide⟩),
   pushAt 1995 1 31,
   opAt 1996 .NOT,
   opAt 1997 .ADD,
   opAt 1998 (.Swap ⟨0, by decide⟩),
   pushAt 1999 2 2666,
   opAt 2000 .JUMPI]

/-- The limb-pass body up to its exit test (`blk3077` instructions 0..42). -/
def blk3077a :
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
   opAt 2228 .ADD]

/-- The exit test of the limb-pass body (`blk3077` instructions 43..47). -/
def blk3077b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 2340 2 2080,
   opAt 2341 (.Dup ⟨1, by decide⟩),
   opAt 2342 .GT,
   pushAt 2343 2 2951,
   opAt 2344 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
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
   opAt 2409 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2410 (.Swap ⟨0, by decide⟩),
   pushAt 2411 1 31,
   opAt 2412 .NOT,
   opAt 2413 .ADD,
   pushAt 2414 2 2111,
   opAt 2415 (.Dup ⟨1, by decide⟩),
   opAt 2416 .GT,
   pushAt 2417 2 3168,
   opAt 2418 .JUMPI]

/-- The subtract-round body up to its exit test (`blk3213` instructions 0..22). -/
def blk3213a :
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
   opAt 2464 .OR]

/-- The exit test of the subtract-round body (`blk3213` instructions 23..31). -/
def blk3213b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2465 (.Swap ⟨1, by decide⟩),
   opAt 2466 .POP,
   pushAt 2467 1 31,
   opAt 2468 .NOT,
   opAt 2469 .ADD,
   pushAt 2470 2 2111,
   opAt 2471 (.Dup ⟨1, by decide⟩),
   opAt 2472 .GT,
   pushAt 2473 2 3247,
   opAt 2474 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
