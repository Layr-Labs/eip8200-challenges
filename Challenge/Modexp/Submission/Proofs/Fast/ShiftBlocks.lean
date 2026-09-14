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
   pushAt 1995 2 2662,
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
   pushAt 2339 2 2947,
   opAt 2340 .JUMPI]

/-- The add-round body up to its exit test (`blk3157` instructions 0..26). -/
def blk3157a :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2379 .JUMPDEST,
   opAt 2380 (.Dup ⟨0, by decide⟩),
   opAt 2381 .MLOAD,
   opAt 2382 (.Dup ⟨1, by decide⟩),
   pushAt 2383 2 2112,
   opAt 2384 (.Swap ⟨0, by decide⟩),
   opAt 2385 .SUB,
   opAt 2386 .MLOAD,
   opAt 2387 (.Dup ⟨1, by decide⟩),
   opAt 2388 .ADD,
   opAt 2389 (.Dup ⟨0, by decide⟩),
   opAt 2390 (.Dup ⟨2, by decide⟩),
   opAt 2391 .GT,
   opAt 2392 (.Swap ⟨1, by decide⟩),
   opAt 2393 .POP,
   opAt 2394 (.Dup ⟨3, by decide⟩),
   opAt 2395 .ADD,
   opAt 2396 (.Dup ⟨0, by decide⟩),
   opAt 2397 (.Dup ⟨4, by decide⟩),
   opAt 2398 .GT,
   opAt 2399 (.Swap ⟨3, by decide⟩),
   opAt 2400 .POP,
   opAt 2401 (.Dup ⟨2, by decide⟩),
   opAt 2402 .MSTORE,
   opAt 2403 (.Swap ⟨0, by decide⟩),
   opAt 2404 (.Swap ⟨1, by decide⟩),
   opAt 2405 .OR]

/-- The exit test of the add-round body (`blk3157` instructions 27..34). -/
def blk3157b :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2406 (.Swap ⟨0, by decide⟩),
   pushAt 2407 1 31,
   opAt 2408 .NOT,
   opAt 2409 .ADD,
   pushAt 2410 2 2111,
   opAt 2411 (.Dup ⟨1, by decide⟩),
   opAt 2412 .GT,
   pushAt 2413 2 3164,
   opAt 2414 .JUMPI]

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
   pushAt 2463 1 31,
   opAt 2464 .NOT,
   opAt 2465 .ADD,
   pushAt 2466 2 2111,
   opAt 2467 (.Dup ⟨1, by decide⟩),
   opAt 2468 .GT,
   pushAt 2469 2 3243,
   opAt 2470 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast
